module CCGs

import Base.Iterators: product, flatten
import StaticArrays: SVector, @SVector
import ..LambdaCalculus 
import ..LambdaCalculus: LambdaTerm, lambda_reduce, compose, beautify, ≃
import ..Utils: find_first, definition_macro_builder

##############
# Categories #
##############


abstract type SyntacticType end

struct PrimitiveSyntacticType <: SyntacticType
    name::Symbol
    features::Vector{Symbol}
end

name(p::PrimitiveSyntacticType) = p.name
features(p::PrimitiveSyntacticType) = p.features

function (p::PrimitiveSyntacticType)(features_::Vararg{Symbol,N}) where {N}
    PrimitiveSyntacticType(name(p), [features(p)..., features_...])
end

const Direction = Union{Val{:right}, Val{:left}}
const Right = Val{:right}
const Left = Val{:left}

struct ComplexSyntacticType{D <: Direction} <: SyntacticType
    res::SyntacticType
    arg::SyntacticType
end

res(c::ComplexSyntacticType) = c.res

arg(c::ComplexSyntacticType) = c.arg

direction(c::ComplexSyntacticType{D}) where {D} = D

Base.:/(c1::SyntacticType, c2::SyntacticType) =
    ComplexSyntacticType{Right}(c1, c2)

Base.:\(c1::SyntacticType, c2::SyntacticType) =
    ComplexSyntacticType{Left}(c1, c2)

Base.string(p::PrimitiveSyntacticType) =
    isempty(features(p)) ? string(name(p)) : "$(name(p))($(join(features(p), ',')))"

Base.string(c::ComplexSyntacticType{Right}) =
    string(res(c)) * '/' * string(arg(c))

Base.string(c::ComplexSyntacticType{Left}) =
    string(res(c)) * '\\' * string(arg(c))

Base.show(io::IO, c::SyntacticType) = print(io, string(c))

# whether q agrees with p
function agrees(p::PrimitiveSyntacticType, q::PrimitiveSyntacticType)
    name(p) == name(q) &&
    all(feature in features(q) for feature in features(p))
end

agrees(p::PrimitiveSyntacticType, c::ComplexSyntacticType) = false
agrees(c::ComplexSyntacticType, p::PrimitiveSyntacticType) = false

# whether d agrees with c
function agrees(c::ComplexSyntacticType, d::ComplexSyntacticType)
    direction(c) == direction(d) && agrees(res(c), res(d)) &&
    agrees(arg(c), arg(d))
end

struct Category
    syntactic_type::SyntacticType
    logical_form::LambdaTerm
end

syntactic_type(c::Category) = c.syntactic_type

logical_form(c::Category) = c.logical_form

# agrees c2 with c1
function agrees(c1::Category, c2::Category) 
    agrees(c1.syntactic_type, c2.syntactic_type) &&
    lambda_reduce(c1.logical_form) ≃ lambda_reduce(c2.logical_form)
end

function ≃(c1::Category, c2::Category) 
    c1.syntactic_type == c2.syntactic_type &&
    lambda_reduce(c1.logical_form) ≃ lambda_reduce(c2.logical_form)
end

macro primitive_syntactic_type(names...)
    constructor = name->PrimitiveSyntacticType(name, Vector{Symbol}())
    definition_macro_builder(names, constructor)
end

#################
# Lexical Entry #
#################

struct LexicalEntry
    lexeme::String
    cat::Category
end

LexicalEntry(lexeme::String, syn_type::SyntacticType, lf::LambdaTerm) =
    LexicalEntry(lexeme, Category(syn_type, lf))

lexeme(lexical_entry::LexicalEntry) = lexical_entry.lexeme
category(lexical_entry::LexicalEntry) = lexical_entry.cat

struct Lexicon 
    lexical_entries::Vector{LexicalEntry}
end

lexical_entries(lexicon::Lexicon) = lexicon.lexical_entries

Base.iterate(lexicon::Lexicon) = iterate(lexical_entries(lexicon))
Base.iterate(lexicon::Lexicon, state::Int64) =
    iterate(lexical_entries(lexicon), state)

function Base.merge(lexicons::Vararg{Lexicon,N}) where {N}
    Lexicon(collect(union(map(lexicon->Set(lexical_entries(lexicon)),
                              lexicons)...)))
end

struct CombinatoryCategorialGrammar
    lexicon::Lexicon
    type_shifting_rules::Dict{String,Vector{Category}}
end

lexicon(g::CombinatoryCategorialGrammar) = g.lexicon

type_shifting_rules(g::CombinatoryCategorialGrammar) = g.type_shifting_rules

function type_shifted_lexical_entries(g::CombinatoryCategorialGrammar)
    result = lexical_entries(lexicon(g))
    for entry in lexical_entries(lexicon(g))
        for new_category in get(type_shifting_rules(g), lexeme(entry), [])
            push!(result, LexicalEntry(lexeme(entry), new_category))
        end
    end
    result
end

##################
# CCG Operations #
##################

"""
dir == LEFT means left(right)
dir == RIGHT means right(left)
"""

abstract type InvalidCCGOperation <: Exception end

struct InvalidApplication <: InvalidCCGOperation end
struct InvalidComposition <: InvalidCCGOperation end

function apply(left::Category, right::Category, dir::Type{<:Direction})
    operator, operand = dir isa Type{Right} ? (left, right) : (right, left)
    if syntactic_type(operator) isa ComplexSyntacticType{dir} &&
        agrees(arg(syntactic_type(operator)), syntactic_type(operand))
        Category(res(syntactic_type(operator)),
                 beautify(lambda_reduce(logical_form(operator)(logical_form(operand)))))
    else
        throw(InvalidApplication())
    end
end

function compose(left::Category, right::Category, dir::Type{<:Direction})
    operator, operand = dir isa Type{Right} ? (left, right) : (right, left)
    syntactic_type_combinator = dir isa Type{Right} ? Base.:/ : Base.:\
    if syntactic_type(operator) isa ComplexSyntacticType{dir} &&
       syntactic_type(operand) isa ComplexSyntacticType{dir} &&
       agrees(arg(syntactic_type(operator)), res(syntactic_type(operand)))
        Category(syntactic_type_combinator(res(syntactic_type(operator)),
                                           arg(syntactic_type(operand))),
                 beautify(compose(logical_form(operator), logical_form(operand))))
    else
        throw(InvalidComposition())
    end
end

###############
# Parse Trees #
###############

abstract type CCGParseTreeNode end

abstract type CCGParseTreeInternalNode <: CCGParseTreeNode end


struct CCGParseTreeLeaf <: CCGParseTreeNode
    lexical_entry::LexicalEntry
end

CCGParseTreeLeaf(lexeme::String, category::Category) = 
    CCGParseTreeLeaf(LexicalEntry(lexeme, category))

category(node::CCGParseTreeLeaf) = category(lexical_entry(node))

lexical_entry(leaf::CCGParseTreeLeaf) = leaf.lexical_entry

const CategoryApplication = Val{:application}
const CategoryComposition = Val{:composition}
const CCGBinaryOps = Union{CategoryApplication, CategoryComposition}

struct BinaryInternalNode{Op<:CCGBinaryOps, D<:Direction} <: CCGParseTreeInternalNode
    left::CCGParseTreeNode
    right::CCGParseTreeNode
    cat::Category
end

children(node::BinaryInternalNode) = (node.left, node.right)

left_child(node::BinaryInternalNode) = node.left

right_child(node::BinaryInternalNode) = node.right

category(node::CCGParseTreeInternalNode) = node.cat

function BinaryInternalNode{Op, D}(left_child::CCGParseTreeNode,
                                   right_child::CCGParseTreeNode) where
                                    {Op <: CCGBinaryOps, D <: Direction}
    operation = Op isa Type{CategoryApplication} ? apply : compose
    BinaryInternalNode{Op, D}(left_child, right_child,
                              operation(category(left_child),
                                        category(right_child), D))
end

struct UnaryInternalNode <: CCGParseTreeInternalNode 
    child::CCGParseTreeNode
    cat::Category
end

children(node::UnaryInternalNode) = (node.child,)

child(node::UnaryInternalNode) = node.child

###########
# Parsing #
###########

const PUNCTUATION = @SVector(['.', ',', '?'])

remove_punctuation(token::String) = strip(token, PUNCTUATION)

function chart_parse(sentence::String, grammar::CombinatoryCategorialGrammar)
    lexemes = map(string ∘ remove_punctuation ∘ lowercase, split(sentence))
    n = length(lexemes)
    chart = make_chart(n)
    populate_first_row!(chart, lexemes, grammar)
    for span=2:n, beg=1:n-span+1, l=1:span-1
        parent_cats = product(chart[l][beg], chart[span-l][beg+l])
        new_cats = collect(flatten([cat_combinations(left, right)
                                    for (left, right) in parent_cats]))
        append!(chart[span][beg], new_cats)
    end
    chart[n][1]
end

function make_chart(n::Int)
    SVector{n}([SVector{n - i + 1}([Vector{CCGParseTreeNode}() for j=1:n-i+1])
                for i=1:n])
end

function populate_first_row!(chart, lexemes, grammar)
    for (i, lexeme_) in enumerate(lexemes)
        append!(chart[1][i], [CCGParseTreeLeaf(entry) for entry in lexicon(grammar)
                              if lexeme(entry) == lexeme_])
        additional_categories = get(type_shifting_rules(grammar), lexeme_, [])
        append!(chart[1][i], [CCGParseTreeLeaf(lexeme_, category)
                              for category in additional_categories])
    end
end

function cat_combinations(left::CCGParseTreeNode, right::CCGParseTreeNode)
    new_nodes = Vector{CCGParseTreeNode}()
    for (op, dir) in product((CategoryApplication, CategoryComposition), (Left, Right))
        try
            push!(new_nodes, BinaryInternalNode{op, dir}(left, right))
        catch e
            e isa InvalidCCGOperation || rethrow(e)
        end
    end
    new_nodes
end


###############
# Realization #
###############

realization(leaf::CCGParseTreeLeaf) = [lexeme(lexical_entry(leaf))]
realization(node::BinaryInternalNode) = [realization(left_child(node))...,
                                         realization(right_child(node))...]
realization(node::UnaryInternalNode) = realization(child(node))

struct RealizationHint
    applies::Function
    apply_hint::Function
end

applies(hint::RealizationHint, cat::Category) = hint.applies(cat)

apply_hint(hint, cat, grammar, hints) = hint.apply_hint(cat, grammar, hints)

function realize(cat::Category, grammar::CombinatoryCategorialGrammar;
                 hints=[], max_depth=6)
    hint = find_first(hint->applies(hint, cat), hints)
    if !isnothing(hint)
        return apply_hint(hint, cat, grammar, hints)
    end
    realized = Vector{CCGParseTreeNode}(map(CCGParseTreeLeaf,
                                            type_shifted_lexical_entries(grammar)))
    explored(node) = any(n->category(n) ≃ category(node), realized)
    depth = 1
    while depth <= max_depth
        parse = find_first(node->agrees(cat, category(node)), realized)
        if !isnothing(parse) return parse end
        frontier = collect(flatten(cat_combinations(l, r) for (l, r) in
                                   product(realized, realized)))
        for (i, node) in enumerate(frontier)
            if !explored(node)
                push!(realized, node)
            end
        end
        depth += 1
    end
end

end #module CCGs
