# Exercise_Example: An Exercise Sheet in Three Variants

This session is an example of the ontology `Exercise`: one exercise sheet
(`Exercise_Sheet.thy`) that is typeset three times, for the *students* (the
tasks), for the *professors* (additionally the solutions) and for the
*examiners* (additionally the remarks on the marking). The variants are
selected by the option `document_variants` of the `ROOT` file in
`Isabelle_DOF-Ontologies`:

    document_variants = "student:professor:examiner"

It shows the structure of a sheet (a monitor with exercises, parts, tasks and
subtasks), solutions that refer to their task, remarks, the use of Isabelle
terms and theorems in the text, grid tables, and the command `exercise_role`.

## Building

```console
foo@bar:~$ isabelle build -D Isabelle_DOF-Ontologies Isabelle_DOF-Exercise-Example
```

The three PDFs are generated into the directory `Exercise_Example/output`:
`student.pdf`, `professor.pdf` and `examiner.pdf`.
