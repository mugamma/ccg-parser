module Utils

function find_first(pred::Function, iterable)
    for element in iterable
        if pred(element)
            return element
        end
    end
    nothing
end

function definition_macro_builder(names, constructor)
    clean_names = [split(string(name), ".")[end] for name in names]
    Expr(:block,
         [:($(esc(name)) = $constructor(Symbol($clean_name)))
          for (name, clean_name) in zip(names, clean_names)]...)
end

end # module Utils
