module CCGVis

import ..CCGs: PrimitiveSyntacticType, ComplexSyntacticType, CCGParseTreeNode,
               CCGParseTreeLeaf, CCGParseTreeInternalNode, UnaryInternalNode,
               BinaryInternalNode, Direction, Left, Right, CategoryComposition,
               CategoryApplication, category, lexical_entry, lexeme, children,
               syntactic_type, logical_form
import ..LambdaCalculus: Identifier, Application, Abstraction, name, var, body,
                         operator, operand
import ..LambdaLogic: PredicateFormula, Predicate, predicate, arguments,
                      Conjunction, conjuncts
import PyPlot

###################
# LaTeX Rendering #
###################

#export to_latex, generate_latex_parse_tree, render_parse_tree_latex

function to_latex(c::PrimitiveSyntacticType)
    splitted = split(string(c.name), "_")
    if length(splitted) == 1
        string(c.name)
    else
        "$(splitted[1])_{\\textrm{$(splitted[2])}}"
    end
end

to_latex(c::ComplexSyntacticType{D}) where {D <: Direction} =
    to_latex(c.res) * (D isa Type{Left} ? "\\backslash " : '/') * to_latex(c.arg)

to_latex(t::Identifier) =
    let s=string(name(t)); length(s) == 1 ? s : "\\textrm{$s}" end

to_latex(t::Abstraction) = "\\lambda $(to_latex(var(t))).\\ $(to_latex(body(t)))"

to_latex(t::Application) = "($(to_latex(operator(t))) \\ $(to_latex(operand(t))))"

to_latex(t::PredicateFormula) =
    "($(to_latex(predicate(t))) \\ $(join(map(to_latex, arguments(t)), " \\ ")))"

to_latex(t::Predicate) = "\\textrm{$(name(t))}"

to_latex(c::Conjunction) = join(map(to_latex, conjuncts(c)), " \\land ")

latex_arrow(n::CCGParseTreeLeaf) = "\\hrulefill"
latex_arrow(n::UnaryInternalNode) = "\\hrulefill"
latex_arrow(n::BinaryInternalNode{CategoryApplication,Right}) =
    "\\hrulefill\\raisebox{-2pt}{\$>\$}"
latex_arrow(n::BinaryInternalNode{CategoryApplication,Left}) =
    "\\hrulefill\\raisebox{-2pt}{\$<\$}"
latex_arrow(n::BinaryInternalNode{CategoryComposition,Right}) =
    "\\hrulefill\\raisebox{-2pt}{\$B>\$}"
latex_arrow(n::BinaryInternalNode{CategoryComposition,Left}) =
    "\\hrulefill\\raisebox{-2pt}{\$B<\$}"


############################
# Parse Tree Visualization #
############################


abstract type RowEntry end

struct CategoryRowEntry <: RowEntry
    span::Tuple{Int,Int}
    node::CCGParseTreeInternalNode
end

struct LexemeRowEntry <: RowEntry
    span::Tuple{Int,Int}
    node::CCGParseTreeLeaf
end

span(entry::RowEntry) = entry.span
node(entry::RowEntry) = entry.node

first(t::Tuple) = t[1]
second(t::Tuple) = t[2]

# Text Extractors
syntactic_type_extractor(entry::RowEntry) =
    '$' * to_latex(syntactic_type(category(node(entry)))) * '$'

logical_form_extractor(entry::RowEntry) =
    '$' * to_latex(logical_form(category(node(entry)))) * '$'

arrow_extractor(entry::RowEntry) = latex_arrow(node(entry))

lexeme_extractor(entry::LexemeRowEntry) =
    '$' * "\\textrm{$(lexeme(lexical_entry(node(entry))))}" * '$'


function generate_latex_parse_tree(root::CCGParseTreeNode)
    row_entries = generate_row_entries(root)
    table_rows = []
    push!(table_rows, latex_table_row(row_entries[1], lexeme_extractor))
    for row in row_entries[1:end]
        for extractor in (arrow_extractor, syntactic_type_extractor,
                          logical_form_extractor,)
            push!(table_rows, latex_table_row(row, extractor))
        end
    end
    header = "\\begin{tabular}{$(repeat("c", length(row_entries[1])))}\n"
    header * join(table_rows, "\n") * "\n\\end{tabular}"
end

function generate_row_entries(root::CCGParseTreeNode)
    row_entries = [[]]
    function populate_row_entries(node::CCGParseTreeInternalNode)
        spans, rows = zip(map(populate_row_entries, children(node))...)
        row_idx = 1 + maximum(rows)
        span = (minimum(first, spans), maximum(second, spans))
        while length(row_entries) < row_idx push!(row_entries, []) end
        push!(row_entries[row_idx], CategoryRowEntry(span, node))
        span, row_idx
    end
    function populate_row_entries(node::CCGParseTreeLeaf)
        span = (length(row_entries[1]) + 1, length(row_entries[1]) + 2)
        push!(row_entries[1], LexemeRowEntry(span, node))
        span, 1
    end
    populate_row_entries(root)
    row_entries
end

function latex_table_row(row_entries, text_extractor::Function)
    cur_pos::Int, tokens::Vector{String} = 1, []
    for entry in row_entries
        shift = first(span(entry)) - cur_pos
        width = second(span(entry)) - first(span(entry)) 
        if shift > 0
            append!(tokens, fill("", shift))
            cur_pos += shift
        end
        push!(tokens, "\\multicolumn{$width}{c}{$(text_extractor(entry))}")
        cur_pos += width
    end
    join(tokens, " & ") * "\\\\"
end

function render_parse_tree_latex(root::CCGParseTreeNode)
    pt = """\\documentclass{standalone}
            \\begin{document}
            $(generate_latex_parse_tree(root))
            \\end{document}"""
    open("/tmp/src.tex", "w") do io print(io, pt) end
    run(pipeline(`pdflatex -output-directory /tmp /tmp/src.tex`;
                 stdout=devnull, stderr=devnull))
    run(pipeline(`convert -density 800x800 /tmp/src.pdf -quality 100 -flatten
                 -colorspace Gray /tmp/pt.png`; stdout=devnull, stderr=devnull))
    PyPlot.figure(;figsize=(30, 60));
    ax = PyPlot.axes();
    ax.axis("off")
    ax.imshow(PyPlot.imread("/tmp/pt.png"); cmap="gray")
end

end # module CCGVis
