module LambdaCalculus

import ..Utils: definition_macro_builder

#export LambdaTerm, Constant, Variable, Identifier, Abstraction, Application,
       #lambda, alpha_convert, beta_reduce, eta_reduce, alpha_equivalent, ≃,
       #lambda_reduce, compose, beautify, name, var, body, operator, operand


#########
# Types #
#########

abstract type LambdaTerm end

struct Constant <: LambdaTerm
    name::Symbol
end

struct Variable <: LambdaTerm
    name::Symbol
end

const Identifier = Union{Constant,Variable}

name(identifier::Identifier) = identifier.name

struct Abstraction <: LambdaTerm
    var::Variable
    body::LambdaTerm
end

var(abs::Abstraction) = abs.var

body(abs::Abstraction) = abs.body

struct Application <: LambdaTerm
    operator::LambdaTerm
    operand::LambdaTerm
end

operator(app::Application) = app.operator

operand(app::Application) = app.operand


free_vars(var::Variable) = Set{Variable}((var,))

free_vars(constant::Constant) = Set{Variable}()

free_vars(abs::Abstraction) = setdiff(free_vars(body(abs)), (var(abs),))

free_vars(app::Application) = union(free_vars(operator(app)),
                                    free_vars(operand(app)))

bound_vars(var::Identifier) = Set{Variable}()

bound_vars(abs::Abstraction) = union(bound_vars(body(abs)), (var(abs),))

bound_vars(app::Application) = union(bound_vars(operator(app)),
                                     bound_vars(operand(app)))

all_vars(term::LambdaTerm) = union(free_vars(term), bound_vars(term))

######################
# Construction Sugar #
######################

macro variable(names...)
    definition_macro_builder(names, Variable)
end

macro constant(names...)
    definition_macro_builder(names, Constant)
end

lambda(var::Variable, body::LambdaTerm) = Abstraction(var, body)

lambda(var::Symbol, body::LambdaTerm) = lambda(Variable(var), body)

lambda(var::Symbol, body::Symbol) = lambda(Variable(var), Variable(body))

(operator::LambdaTerm)(operand::LambdaTerm) = Application(operator, operand)

(operator::Symbol)(operand::LambdaTerm) = Variable(operator)(operand)

(operator::LambdaTerm)(operand::Symbol) = operator(Variable(operand))

(operator::Symbol)(operand::Symbol) = Variable(operator)(Variable(operand))

apply(f::LambdaTerm, x::LambdaTerm) = f(x)

######
# IO #
######

Base.string(identifier::Identifier) = string(name(identifier))

Base.string(f::Abstraction) = "λ$(var(f)).$(string(body(f)))"

Base.string(a::Application) = "($(string(operator(a))) $(string(operand(a))))"

Base.show(io::IO, exp::LambdaTerm) = print(io, string(exp))

################
# α-conversion #
################

function alpha_convert(abs::Abstraction, new_var::Variable)
    if !(new_var in free_vars(abs)) && !(new_var in bound_vars(abs))
        rename_var(abs, var(abs), new_var)
    else
        error("Invalid α-conversion: $new_var is free or bound in $abs")
    end
end

alpha_convert(abs::Abstraction, new_var::Symbol) =
    alpha_convert(abs, Variable(new_var))

rename_var(identifier::Identifier, from::Variable, to::Variable) =
    identifier == from ? to : identifier

rename_var(abs::Abstraction, from::Variable, to::Variable) = 
    lambda(rename_var(var(abs), from, to), rename_var(body(abs), from , to))

rename_var(app::Application, from::Variable, to::Variable) = 
    rename_var(operator(app), from, to)(rename_var(operand(app), from, to));

#################
# α-equivalence #
#################

function random_neither_free_nor_bound_var(terms::Vararg{LambdaTerm, N}) where N
    unacceptable_vars = union(map(free_vars, terms), map(bound_vars, terms))
    n = rand(Int)
    while Variable(Symbol('#', n)) in unacceptable_vars
        n = rand(Int)
    end
    Variable(Symbol('#', n))
end

alpha_equivalent(v::Identifier, u::Identifier) = v == u

function alpha_equivalent(f::Abstraction, g::Abstraction)
    new_arg = random_neither_free_nor_bound_var(f, g)
    alpha_equivalent(body(alpha_convert(f, new_arg)),
                     body(alpha_convert(g, new_arg)))
end

alpha_equivalent(s::Application, t::Application) =
    alpha_equivalent(operator(s), operator(t)) &&
    alpha_equivalent(operand(s), operand(t))

# XXX risky! add tests
alpha_equivalent(s::LambdaTerm, t::Union{LambdaTerm,Nothing}) = false

≃(x, y) = alpha_equivalent(x, y)


###############
# β-reduction #
###############

substitute(constant::Constant, from::Variable, to::LambdaTerm) = constant

substitute(var::Variable, from::Variable, to::LambdaTerm) =
    var == from ? to : var

function substitute(abs::Abstraction, from::Variable, to::LambdaTerm)
    if var(abs) == from 
        abs
    elseif !(var(abs) in free_vars(to) && from in free_vars(abs))
        lambda(var(abs), substitute(body(abs), from, to))
    else
        new_var = random_neither_free_nor_bound_var(abs, to, from)
        lambda(new_var,
               substitute(rename_var(body(abs), var(abs), new_var), from, to))
    end
end

substitute(app::Application, from::Variable, to::LambdaTerm) =
    substitute(operator(app), from, to)(substitute(operand(app), from, to))

function beta_reduce(app::Application)
    if operator(app) isa Abstraction
        substitute(body(operator(app)), var(operator(app)), operand(app))
    else
        app
    end
end

###############
# η-reduction #
###############


function is_eta_redex(abs::Abstraction)
    body(abs) isa Application && var(abs) == operand(body(abs)) 
end

eta_reduce(abs::Abstraction) = is_eta_redex(abs) ? operator(body(abs)) : abs

#########
# Misc. #
#########

lambda_reduce(identifier::Identifier, _::Union{Nothing,LambdaTerm}=nothing) =
     identifier

function lambda_reduce(app::Application,
                       prev_term::Union{Nothing,LambdaTerm}=nothing)
    if app ≃ prev_term
        app
    else
        lambda_reduce(beta_reduce(apply(lambda_reduce(operator(app)),
                                        lambda_reduce(operand(app)))), app)
    end
end

function lambda_reduce(abs::Abstraction,
                       prev_term::Union{Nothing,LambdaTerm}=nothing)
    if abs ≃ prev_term
        abs
    else
        simplified = eta_reduce(abs)
        if simplified isa Abstraction
            lambda_reduce(lambda(var(simplified), lambda_reduce(body(simplified))), abs)
        else
            lambda_reduce(simplified)
        end
    end
end


function compose(f::Abstraction, g::Abstraction)
    new_var = random_neither_free_nor_bound_var(f, g)
    lambda(new_var, lambda_reduce(f(g(new_var))))
end

function beautify(term::LambdaTerm)
    term_vars = all_vars(term)
    nice_vars = setdiff(Set(map(i->Variable(Symbol('a' + i)), 0:25)), term_vars)
    reduce((term, v)-> rename_var(term, v, pop!(nice_vars)),
           filter(v->startswith(string(v), '#'), term_vars);
           init=term)
end

end # module LambdaCalculus
