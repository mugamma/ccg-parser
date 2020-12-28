module LambdaLogic

import ..LambdaCalculus
import ..LambdaCalculus: Constant, LambdaTerm, Variable


struct Predicate{Arity}
    name::Constant
end

name(p::Predicate) = p.name

macro predicate(args...)
    clean_names = [split(string(name), ".")[end] for name in args[1:end-1]]
    arity = args[end]
    Expr(:block,
         [:($(esc(name)) = Predicate{$arity}(Symbol($clean_name)))
          for (name, clean_name) in zip(args[1:end-1], clean_names)]...)
end

Predicate{Arity}(name::Symbol) where {Arity} = Predicate{Arity}(Constant(name))

LambdaCalculus.name(p::Predicate)= name(p)

LambdaCalculus.free_vars(p::Predicate) = Set{Variable}()

LambdaCalculus.bound_vars(p::Predicate) = Set{Variable}()

Base.string(p::Predicate) = string(name(p))

Base.show(io::IO, p::Predicate) = print(io, string(p))

LambdaCalculus.lambda_reduce(p::Predicate,
                             _::Union{Nothing,LambdaTerm}=nothing) = p

LambdaCalculus.alpha_equivalent(p::Predicate, q::Predicate) = p == q

struct PredicateFormula{Arity} <: LambdaTerm
    predicate::Predicate{Arity}
    arguments::NTuple{Arity,LambdaTerm}
end

predicate(app::PredicateFormula) = app.predicate

arguments(app::PredicateFormula) = app.arguments


function LambdaCalculus.free_vars(app::PredicateFormula)
    union(LambdaCalculus.free_vars(predicate(app)),
          map(LambdaCalculus.free_vars, arguments(app)))
end

function LambdaCalculus.bound_vars(app::PredicateFormula)
    union(LambdaCalculus.bound_vars(predicate(app)),
          map(LambdaCalculus.bound_vars, arguments(app)))
end

function (predicate::Predicate{Arity})(arguments::Vararg{LambdaTerm,Arity}) where {Arity}
    PredicateFormula{Arity}(predicate, arguments)
end

function Base.string(app::PredicateFormula) 
    "($(predicate(app)) $(join(arguments(app), ' ')))"
end

function LambdaCalculus.rename_var(app::PredicateFormula,
                                   from::Variable, to::Variable)
    predicate(app)(map(t->LambdaCalculus.rename_var(t, from, to),
                       arguments(app))...)
end

function LambdaCalculus.substitute(app::PredicateFormula,
                                   from::Variable, to::LambdaTerm)
    predicate(app)(map(t->LambdaCalculus.substitute(t, from, to),
                       arguments(app))...)
end

function LambdaCalculus.lambda_reduce(app::PredicateFormula,
                                  prev_term::Union{Nothing,LambdaTerm}=nothing)
    if LambdaCalculus.alpha_equivalent(app, prev_term)
        app
    else
        simplified_args = map(LambdaCalculus.lambda_reduce, arguments(app))
        LambdaCalculus.lambda_reduce(predicate(app)(simplified_args...), app)
    end
end

function LambdaCalculus.alpha_equivalent(papp::PredicateFormula{N},
                                         qapp::PredicateFormula{M}) where {N, M}
    N == M && predicate(papp) == predicate(qapp) &&
    all(LambdaCalculus.alpha_equivalent(parg, qarg)
        for (parg, qarg) in zip(arguments(papp), arguments(qapp)))
end

# XXX For now. I will make this properly typed
struct Conjunction <: LambdaTerm
    conjuncts::Vector{LambdaTerm}
end

conjuncts(c::Conjunction) = c.conjuncts

function and(terms::Vararg{LambdaTerm,N}) where {N} 
    flattened = []
    for term in terms
        if term isa Conjunction
            append!(flattened, conjuncts(term))
        else
            push!(flattened, term)
        end
    end
    Conjunction(flattened)
end

function LambdaCalculus.free_vars(c::Conjunction)
    union(map(LambdaCalculus.free_vars, conjuncts(c))...)
end

function LambdaCalculus.bound_vars(c::Conjunction)
    union(map(LambdaCalculus.bound_vars, conjuncts(c))...)
end

function Base.string(c::Conjunction)
    "($(join(conjuncts(c), "∧")))"
end

function LambdaCalculus.rename_var(c::Conjunction,
                                   from::Variable, to::Variable)
    and(map(t->LambdaCalculus.rename_var(t, from, to), conjuncts(c))...)
end

function LambdaCalculus.substitute(c::Conjunction,
                                   from::Variable, to::LambdaTerm)
    and(map(t->LambdaCalculus.substitute(t, from, to), conjuncts(c))...)
end

function LambdaCalculus.lambda_reduce(c::Conjunction,
                                  prev_term::Union{Nothing,LambdaTerm}=nothing)
    simplified_conjs = map(LambdaCalculus.lambda_reduce, conjuncts(c))
    Conjunction(simplified_conjs)
end

function LambdaCalculus.alpha_equivalent(c1::Conjunction, c2::Conjunction)
    if length(conjuncts(c1)) != length(conjuncts(c2))
        false
    else
        all(t->any(s->LambdaCalculus.alpha_equivalent(s, t), conjuncts(c2)),
            conjuncts(c1)) &&
        all(t->any(s->LambdaCalculus.alpha_equivalent(s, t), conjuncts(c1)),
            conjuncts(c2))
    end
end

end # module LambdaLogic
