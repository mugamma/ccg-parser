module Logic

import Base.Iterators: product, flatten
import ..Utils: definition_macro_builder

abstract type Term end

struct Constant <: Term
    name::Symbol
end

struct Variable <: Term
    name::Symbol
end

name(t::Term) = t.name

const Binding = Dict{Variable, Constant}

struct BinaryPredicate
    name::Symbol
end

name(p::BinaryPredicate) = p.name

Base.string(identifier::Union{Term,BinaryPredicate}) = string(identifier.name)

Base.show(io::IO, identifier::Union{Term,BinaryPredicate}) =
    print(io, string(identifier))

macro relation(names...)
    definition_macro_builder(names, BinaryPredicate)
end

macro variable(names...)
    definition_macro_builder(names, Variable)
end

macro constant(names...)
    definition_macro_builder(names, Constant)
end

abstract type Formula end

struct BinaryPredicateFormula <: Formula
    predicate::BinaryPredicate
    arguments::Tuple{Term,Term}
end

predicate(f::BinaryPredicateFormula) = f.predicate
arguments(f::BinaryPredicateFormula) = f.arguments

Base.string(p::BinaryPredicateFormula) =
    "$(p.predicate)($(p.arguments[1]), $(p.arguments[2]))"

Base.show(io::IO, p::BinaryPredicateFormula) = print(io, string(p))

(p::BinaryPredicate)(x::Term, y::Term) = BinaryPredicateFormula(p, (x, y))

struct Conjunction <: Formula
    conjuncts::Vector{Formula}
end

Base.string(c::Conjunction) = join(map(string, c.conjuncts), "∧")
Base.show(io::IO, c::Conjunction) = print(io, string(c))

struct HornClause
    antecedent::Conjunction
    consequent::BinaryPredicateFormula
end

Base.string(h::HornClause) = "$(h.antecedent) ⟹ $(h.consequent)"

Base.show(io::IO, h::HornClause) = print(io, string(h))

HornClause(formulas::Vararg{Formula,N}) where N =
    HornClause(Conjunction(collect(formulas[1:end-1])), formulas[end])

struct ExistentiallyQuantifiedStatement
    var::Variable
    formula::Formula
end

Base.string(e::ExistentiallyQuantifiedStatement) = "∃$(e.var).$(e.formula)"

Base.show(io::IO, e::ExistentiallyQuantifiedStatement) = print(io, string(e))

free_vars(p::BinaryPredicateFormula) = Set(filter(a->a isa Variable, p.arguments))

free_vars(c::Conjunction) = union(map(free_vars, c.conjuncts)...)

apply_binding(c::Constant, binding::Binding) = c
apply_binding(v::Variable, binding::Binding) = get(binding, v, v)
apply_binding(p::BinaryPredicateFormula, binding::Binding) = 
    p.predicate(map(t->apply_binding(t, binding), p.arguments)...)
apply_binding(c::Conjunction, binding::Binding) =
    Conjunction(map(p->apply_binding(p, binding), c.conjuncts))

end # module Logic
