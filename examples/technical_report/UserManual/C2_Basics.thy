(*<*)
theory
  "C2_Basics"
imports
  "C1_Installation"
begin
define_shortcut* ijedit \<rightleftharpoons> \<open>Isabelle/jEdit\<close>
declare_reference*[example3::float]
declare_reference*[example2::figure]
declare_reference*[example1::figure]

(*>*)
chapter*[anti::text_section]\<open>Basics\<close>

text\<open>
In this section, you will come to see the mention to \<^ijedit> , this is a reference to
the default user-interface for Isabelle. It is the main application of PIDE, which is the framework
 for Prover IDEs. More information can be found in the Isabelle/jEdit manual \<^cite>\<open>"mwenzel:jedit:2025"\<close>.
\<close>

section*[macro::technical]\<open>Macros\<close>

text\<open>
There is a mechanism for defining document-local macros that are PIDE-supported but expand within
 the integrated source.  This feature allows for the creation of shortcuts as well as macros.
 Usually these are placed at the very beginning of your new document, creating the shorthands that
 will be useful to the writing of your current paper.\<close>

subsection*[shrtcut::technical]\<open>Shortcuts\<close>

text\<open>
Shortcuts serve as shorthands for other commands, typically \<^LaTeX>  enhancing both the readability
 of your \<^isadof> code and the flow of writing.

A simple example of this is my use of the \<^LaTeX> logo in my texts.
You define the shortcut whenever you want in your paper, and then when you want to use 
it you simply use it antiquotation. Usually you will surround the
definition by (*<*) and (*>*) so that it does not appear in the pdf.

\begin{isarbox}
\begin{isabelle}
\isakeywordONE{define{\isacharunderscore}{\kern0pt}shortcut{\isacharasterisk}{\kern0pt}}\ LaTeX\ {\isasymrightleftharpoons}\ {\isacartoucheopen}{\isacharbackslash}{\kern0pt}LaTeX{\isacharbraceleft}{\kern0pt}{\isacharbraceright}{\kern0pt}{\isacartoucheclose}\isanewline
\isakeywordONE{text}{\isacartoucheopen}\end{isabelle}
 You need a full \textit{\textbf{LaTeX}} installation to use the pdf generator of \textit{\textbf{isadof}}
\begin{isabelle}{\isacartoucheclose}\isanewline
\end{isabelle}
\end{isarbox}

%@ {boxed_theory_text [display]\<open>
%  define_shortcut* LaTeX \<rightleftharpoons> \<open>\LaTeX{}\<close>
%  text\<open> You need a full \^LaTeX> installation to use the pdf generator of \isadof.\<close>\<close>}

\begin{outmat}
 You need a full \LaTeX{} installation to use the pdf generator of \isadof{}.
\end{outmat}

%@ {boxed_pdf [display]
%\<open> You need a full \LaTeX installation to use the pdf generator of.\<close>}
\<close>



subsection*[mac::technical]\<open>Macro's\<close>

text\<open>
Macro commands are shortcuts that allow you to give in parameters, or parameterized short-cuts.

Here we may want to create a macro for a specific math symbol from \<^LaTeX>, that repeatedly appears in 
a paper, helping with the overall readibility.

\<^isarbox>\<open>
\begin{isabelle}
\isakeywordONE{define{\isacharunderscore}{\kern0pt}macro{\isacharasterisk}{\kern0pt}}\ sqrt {\isasymrightleftharpoons}\ 
{\isacartoucheopen}{\isacharbackslash}ensuremath{\isacharbraceleft}{\isacharbackslash}{\kern0pt}sqrt{\isacharbraceleft}{\kern0pt}{\isacartoucheclose} {\isacharunderscore}
 {\isacartoucheopen}{\isacharbraceright}{\kern0pt}{\isacharbraceright}{\isacartoucheclose}\isanewline
\isakeywordONE{text}{\isacartoucheopen}\end{isabelle}
 The square root of 121 is written \textit{\textbf{sqrt}}<121> and is equal to 11.
\begin{isabelle}{\isacartoucheclose}\isanewline
\end{isabelle}
\<close>
\begin{outmat}
   The square root of 121 is written $\sqrt{121}$ and is equal to 11.
\end{outmat}
\<close>

section*[lists::technical]\<open>Lists\<close>
text\<open>
There are two ways to create to create lists in \<^isadof>: unordered lists and numbered list.
\<close>
subsection*[blist::introduction]\<open>Unordered lists\<close>
text\<open>Unordered lists are made up of elements that all start with the \<^emph>\<open>item\<close> antiquotation, written
 \<^verbatim>\<open>\<^item>\<close> and displayed in \<^ijedit> as $\blacksquare$.


\<^isarbox>\<open>
  \begin{isabelle}
  \isakeywordONE{text}{\isacartoucheopen}\end{isabelle}
  Let us make a list:
  \begin{itemize}
    \item[$\blacksquare$] list element 
    \item[$\blacksquare$] list element
  \end{itemize}\begin{isabelle}
  {\isacartoucheclose}
  \end{isabelle}
\<close>
\<^outmat>\<open>
  Let us make a list:
  \begin{itemize}
    \item list element 
    \item list element
  \end{itemize}
\<close>
\<close>


subsection*[nlist::technical]\<open>Numbered Lists\<close>
text\<open>Numbered lists are exactly the same but they use the \<^emph>\<open>enum\<close> antiquotation, written \<^verbatim>\<open>\<^enum>\<close> and
 displayed in \<^ijedit> as $\blacktriangleright$.


\<^isarbox>\<open>
  \begin{isabelle}
  \isakeywordONE{text}{\isacartoucheopen}\end{isabelle}
  Let us make a list:
  \begin{enumerate}
    \item[$\blacktriangleright$] list element 
    \item[$\blacktriangleright$] list element
  \end{enumerate}\begin{isabelle}
  {\isacartoucheclose}
  \end{isabelle}
\<close>
\<^outmat>\<open>
  Let us make a list:
  \begin{enumerate}
    \item list element 
    \item list element
  \end{enumerate}
\<close>
\<close>

subsection*[nestlist::technical]\<open>Complex Lists\<close>
text\<open>In \<^isadof>, indentation matters lot in \<^isadof> when making list. This also allows to 
combine ordered and unordered lists, in many ways. Here are a few examples.
\<close>

paragraph\<open>Example 1: Leveled lists\<close>
text\<open>When you use the \<^emph>\<open>enum\<close> antiquotation you can create levels of lists with different labels.
\<^isarbox>\<open>
  \begin{isabelle}
  \isakeywordONE{text}{\isacartoucheopen}\end{isabelle}
  Leveled list:
  \begin{enumerate}
    \item[$\blacktriangleright$] level 1
    \item[$\blacktriangleright$] level 1
      \begin{enumerate}
        \item[$\blacktriangleright$] level 2
        \item[$\blacktriangleright$] level 2
        \begin{enumerate}
          \item[$\blacktriangleright$] level 3 ...
        \end{enumerate}
      \end{enumerate}
    \item[$\blacktriangleright$] level 1
  \end{enumerate}\begin{isabelle}
  {\isacartoucheclose}
  \end{isabelle}
\<close>
\<^outmat>\<open>
  Leveled list:
  \begin{enumerate}
    \item level 1
    \item level 1
      \begin{enumerate}
        \item level 2
        \item level 2
        \begin{enumerate}
          \item level 3 ...
        \end{enumerate}
      \end{enumerate}
    \item level 1
  \end{enumerate}
\<close>
\<close>


paragraph\<open>Example 2: Nested lists\<close>
text\<open>
Similar to the precedent example except we combine ordered and unordered lists.
\<^isarbox>\<open>
  \begin{isabelle}
  \isakeywordONE{text}{\isacartoucheopen}\end{isabelle}
  Let us make a list within a list:
  \begin{enumerate}
    \item[$\blacktriangleright$] list 1 element 1
    \item[$\blacktriangleright$] list 1 element 2
    \begin{itemize}
      \item[$\blacksquare$] list 2 element 1
      \item[$\blacksquare$] list 2 element 2
    \end{itemize}
    \item[$\blacktriangleright$] list 1 element 3
  \end{enumerate}\begin{isabelle}
  {\isacartoucheclose}
  \end{isabelle}
\<close>
\<^outmat>\<open>
  Let us make a list within a list:
  \begin{enumerate}
    \item list 1 element 1
    \item list 1 element 2
    \begin{itemize}
      \item list 2 element 1
      \item list 2 element 2
    \end{itemize}
    \item list 1 element 3
  \end{enumerate}
\<close>
\<close>


text\<open>
The end of a list ins Isabelle/Isar is defined as an empty line in Isabelle, switching type list with no
change in indentation is therefore implicitly also ends a list.
\<close>
subsection*[simpfig::technical]\<open>Simple\<close>

text\<open>The figure macro is provided by the \<^isadof> ontology, and allows you to display a file as
 a figure in your document. The path towards the document (pdf, png) is given in the \<^verbatim>\<open>file_source\<close>
 parameter.This macro has a few others parameter values that you can change such as :
  \<^item> \<^verbatim>\<open>relative_width\<close> (int) : allows you to change the scale of the image. It is equal to the percentage
 of the text width, default value is 100.
  \<^item> \<^verbatim>\<open>relative_height\<close> (int) : allows you to change the scale of the image. It is equal to the percentage
of a document page, default value is 100.
  \<^item> \<^verbatim>\<open>caption\<close> (Isabelle/HOL) : allows you to define a caption for your figure. It is defined within the
 cartouches after the macro, if left empty the caption will be empty as it is it's default value.

For example, if "figures/LatexLogo.png" is the path towards your image in your document folder, the
 following \<^isadof> code:

@{boxed_theory_text[display]\<open>
figure*[example1::figure,relative_width="95",file_src="''figures/LatexLogo.png''"]\<open> 
     Latex Logo on white background \<close>
\<close>
}
produces the result @{figure(unchecked)\<open>example1\<close>}.
\<close>

figure*[example1::figure,relative_width="95",file_src="''figures/LatexLogo.png''"]\<open> 
     Latex Logo on white background \<close>

subsection*[compfid::technical]\<open>Complex\<close>

text\<open>It you wanted a more liberal use of your images/figures you may use the \<^verbatim>\<open>text\<close> macro from the
 \<^isadof> ontology. This has many uses when formatting your document, such as allowing to have figures
 side by side. 
This is easier to understand with examples.
Firstly, an example were we display a single figure, similarly to the use of the \<^verbatim>\<open>figure\<close> macro.

@{boxed_theory_text[display]\<open>
text*[example2::float,  main_caption="''\<open>Latex Logo on white background\<close>''"]
\<open>@{fig_content (width=35, caption="''''") "''figures/LatexLogo.png''"}\<close>
\<close>
}
This has the following results @{figure(unchecked)\<open>example2\<close>}.
\<close>
text*[example2::float,  main_caption="\<open>Latex Logo on white background\<close>"]
\<open>@{fig_content (width=95, caption="") "figures/LatexLogo.png"}\<close>
text\<open>
As you can see this has the exact same result as the example we gave with the \<^verbatim>\<open>figure\<close> macro.
In this second example we see how we can use \<^verbatim>\<open>text\<close> macro to have two figures side by side.

@{boxed_theory_text[display]\<open>
text*[example3::float, 
      main_caption="\<open>Latex logos\<close>"]
\<open>
@{fig_content (width=35, caption="In white") "figures/LatexLogo.png"
}@{fig_content (width=35, caption="In black") "figures/LatexLogoBlack.png"}
\<close>
\<close>
}
This bit of \<^isadof> code would generate this result  @{float(unchecked)\<open>example3\<close>}.
\<close>

text*[example3::float,  main_caption="\<open>Latex logos\<close>"]
\<open>
@{fig_content (width=35, caption="In white") "figures/LatexLogo.png"
}@{fig_content (width=35, caption="In black") "figures/LatexLogoBlack.png"}
\<close>

text\<open>As you can clearly tell the placement seems a bit off. This is because each figure is placed at
 the first available place to the right of the current content. We can resolve this by adding a \<^verbatim>\<open>hs\<open>2.5cm\<close>\<close>
macro command between our two \<^verbatim>\<open>fig_content\<close>, and a \<^verbatim>\<open>hs\<open>0.5cm\<close>\<close> before the first one and after the
 second one.\<close>

text*[example4::float,  main_caption="\<open>Latex logos\<close>"]
\<open>
\<^hs>\<open>0.5cm\<close>@{fig_content (width=35, caption="In white") "figures/LatexLogo.png"
}\<^hs>\<open>2.5cm\<close>@{fig_content (width=35, caption="In black") "figures/LatexLogoBlack.png"}\<^hs>\<open>0.5cm\<close>
\<close>
text\<open> Placing figures within a \<^isadof> document can be predictable but you can play with the
 different tools to get the wanted result. @{float\<open>example4\<close>}\<close>

section*[hlinks::technical]\<open>Hyperlinks\<close>

text\<open>Hyperlinks let you add links to websites. The url antiquotation in \<^isadof> is written \<^verbatim>\<open>\<^url>\<close>.
 Below is an example of creating a hyperlink towards the installation page of \<^isadof>.


\<^isarbox>\<open>\<^isatext>\<open>url
 This is the link where you may install Isabelle/DOF :
\textbf{\textit{url}}<https://www.isa-afp.org/entries/Isabelle\_DOF.html>
\<close>\<close>
\<^outmat>\<open> This is the link where you may install Isabelle/DOF : \\
\url{https://www.isa-afp.org/entries/Isabelle_DOF.html}
\<close>
\<close>

section*[ref::technical]\<open>References\<close>
text\<open> References allow you to create pointers to certain figures and sections in your document
 allowing a quick access and good navigation in your PDF file.\<close>

paragraph\<open>Referencing backwards\<close>
text\<open>This is an easy way to add a reference to chapter,section or figure that has already occured in
your document. 
@{boxed_theory_text[display]\<open>
subsection*[refexample1::technical]\<open>Reference example 1\<close>
text\<open>We have just created a reference to the subsection  @{technical\<open>refexample1\<close>}, defined right above.\<close>
\<close>}
\<^outmat>\<open>
 \begin{isamarkupsubsection*}
[label = {CTWOUNDERSCOREBasicsDOTrefexample1},type = {scholarlyUNDERSCOREpaperDOTtechnical},
 args={label = {CTWOUNDERSCOREBasicsDOTrefexample1},type = {scholarlyUNDERSCOREpaperDOTtechnical},
 IsaUNDERSCORECOLDOTtextUNDERSCOREelementDOTlevel = {}, IsaUNDERSCORECOLDOTtextUNDERSCOREelementDOTreferentiable = {False},
 IsaUNDERSCORECOLDOTtextUNDERSCOREelementDOTvariants = {{STR ''outline'', STR ''document''}},
 scholarlyUNDERSCOREpaperDOTtextUNDERSCOREsectionDOTmainUNDERSCOREauthor = {}, scholarlyUNDERSCOREpaperDOTtextUNDERSCOREsectionDOTfixmeUNDERSCORElist = {}, IsaUNDERSCORECOLDOTtextUNDERSCOREelementDOTlevel = {}, scholarlyUNDERSCOREpaperDOTtechnicalDOTdefinitionUNDERSCORElist = {}, scholarlyUNDERSCOREpaperDOTtechnicalDOTstatus = {description}}]Reference example 1
\end{isamarkupsubsection*}\isamarkuptrue%
\begin{isamarkuptext}
We have just created a reference to the subsection  {\isaDofDOTref[type={scholarlyUNDERSCOREpaperDOTtechnical}]     {CTWOUNDERSCOREBasicsDOTrefexample1}}, defined right above.
\end{isamarkuptext}\isamarkuptrue
\<close>\<close>

paragraph\<open>Referencing forwards\<close>
text\<open>Sometimes, however, one would like to add a future chapter or figure, this also possible to do
although a bit longer, by declaring a references to an object that does not yet exist. \<^isadof> will 
then ignore the fact that is does not know such an object, and will not produce an error. It is important 
to note that if a object is declared and used as a reference but never defined it will create a problem
at the very end of the building.
@{boxed_theory_text[display]\<open>
declare_reference*[refexample2::technical]
text\<open>We have just created a reference to the subsection  @{technical(unchecked)\<open>refexample2\<close>}, defined right beneath.\<close>
subsection*[refexample2::technical]\<open>Reference example 2\<close>
\<close>}
\<^outmat>\<open>          
\isakeywordONE{declare{\isacharunderscore}{\kern0pt}reference{\isacharasterisk}{\kern0pt}}\isamarkupfalse%
{\isacharbrackleft}{\kern0pt}refexample{\isadigit{2}}{\isacharcolon}{\kern0pt}{\isacharcolon}{\kern0pt}technical{\isacharbrackright}{\kern0pt}
\begin{isamarkuptext}
We have just created a reference to the subsection  {\isaDofDOTref[type={scholarlyUNDERSCOREpaperDOTtechnical}]     {CTWOUNDERSCOREBasicsDOTrefexampleTWO}}, defined right beneath.
\end{isamarkuptext}\isamarkuptrue%

\begin{isamarkupsubsection*}
[label = {CTWOUNDERSCOREBasicsDOTrefexampleTWO},type = {scholarlyUNDERSCOREpaperDOTtechnical}, args={label = {CTWOUNDERSCOREBasicsDOTrefexampleTWO},type = {scholarlyUNDERSCOREpaperDOTtechnical}, IsaUNDERSCORECOLDOTtextUNDERSCOREelementDOTlevel = {}, IsaUNDERSCORECOLDOTtextUNDERSCOREelementDOTreferentiable = {False}, IsaUNDERSCORECOLDOTtextUNDERSCOREelementDOTvariants = {{STR ''outline'', STR ''document''}}, scholarlyUNDERSCOREpaperDOTtextUNDERSCOREsectionDOTmainUNDERSCOREauthor = {}, scholarlyUNDERSCOREpaperDOTtextUNDERSCOREsectionDOTfixmeUNDERSCORElist = {}, IsaUNDERSCORECOLDOTtextUNDERSCOREelementDOTlevel = {}, scholarlyUNDERSCOREpaperDOTtechnicalDOTdefinitionUNDERSCORElist = {}, scholarlyUNDERSCOREpaperDOTtechnicalDOTstatus = {description}}]Reference example 2
\end{isamarkupsubsection*}\isamarkuptrue
\<close>
\<close>


section*[cit::technical]\<open>Citations and Bibliography\<close>
text\<open>Providing a bibliography, is vital to  writing accurate papers and reports. It allows people to
the sources as well as know where to go for more information on the subject, it is why \<^isadof> uses
\<^BibTeX>  (\<^url>\<open>https://www.bibtex.org/Using/\<close>) to generate its bibliography.
 
For this you need a 'root.bib' file that will be in the document directory of your paper. Here is an 
example, with the extract of the 'root.bib' file, of the code and the generated end result. 

\begin{config}{root.bib}
@Manual{	  brucker.ea:isabelledof:2025,
  title		= {The Isabelle/DOF User and Implementation Manual},
  author	= {Achim D. Brucker, Nicolas Méric and Burkhart Wolff},
  year		= 2025,
  url     = "www.isa-afp.org/browser_info/current/AFP/Isabelle_DOF/document.pdf"
}
\end{config}

\<^isarbox>\<open>\<^isatext>\<open>
 While writing this user manual,I often used the Implementation and Reference Manual
\textit{\textbf{cite}}<"brucker.ea:isabelledof:2025"> to check on how antiquotations are most often used.
\<close>\<close>
\<^outmat>\<open>
While writing this user manual, I often used the Implementation and \\
 Reference Manual \cite{brucker.ea:isabelledof:2025} to check how antiquotations are most often used.
\<close>
\<close>

section*[footnotes::technical]\<open>Footnotes\<close>
text\<open>Footnotes are often used in academic or technical papers to offer parenthetical or background
 information. In \<^isadof> the footnote antiquotation is written as \<^verbatim>\<open>\<^footnote>\<close>, it appears as the symbol $\P$ in
\<^ijedit>.
\<^isarbox>\<open>\<^isatext>\<open>
Footnotes could be considered references $\P$<You may notice that they appear in the same color, red, as
 references in our PDF>, as they also allow an easy navigation in our document between the footnote
 and it's original paragraph.
\<close>\<close>
\<^outmat>\<open>
Footnotes could be considered references \footnote{You may notice that they appear in the same color, red, as
 references in our PDF}, as in our document they also \\ allow an easy navigation between the footnote
 and it's original paragraph.
\<close>\<close>

section*[tables::technical]\<open>Tables\<close>
text\<open>Currently there is no antiquotation for tables in \<^isadof>, it is however an good way to synthesis 
information. In this section, there will be an example on how to use \<^LaTeX> with \<^isadof> to create 
tables. I suggest checking the \<^LaTeX> documentation online for tables (\<^eg>:\<^cite>\<open>"int:latextable:2020"\<close>) 
many of which go into much more details about the different possibilities.\<close>

text\<open>In this example we will create a table of all defined connective and quantifiers and their definitions
such as they are given in Isabelle HOL. The code that appears below is \<^LaTeX>, but it can be simple put
into any Isar-text environment in your '.thy' file.
@{boxed_latex[display]\<open>
\resizebox{\textwidth}{!}{
\begin{tabular}{|p{0.25\textwidth}|p{0.37\textwidth}|p{0.38\textwidth}|} \hline
\textbf{Name}               & \textbf{Theorem}     & \textbf{Show\_types option}     \\ \hline\hline
@{thm[source]HOL.True_def}  & @{thm HOL.True_def}  & @{thm[show_types]HOL.True_def}  \\ \hline
@{thm[source]HOL.All_def}   & @{thm HOL.All_def}   & @{thm[show_types]HOL.All_def}   \\ \hline
@{thm[source]HOL.Ex_def}    & @{thm HOL.Ex_def}    & @{thm[show_types]HOL.Ex_def}    \\ \hline
@{thm[source]HOL.False_def} & @{thm HOL.False_def} &
 @{thm[show_types]HOL.False_def} \\ \hline
@{thm[source]HOL.not_def}   & @{thm HOL.not_def}   & @{thm[show_types]HOL.not_def}   \\ \hline
@{thm[source]HOL.and_def}   & @{thm HOL.and_def}   & @{thm[show_types]HOL.and_def}   \\ \hline
@{thm[source]HOL.or_def}    & @{thm HOL.or_def}    & @{thm[show_types]HOL.or_def}    \\ \hline
@{thm[source]HOL.Uniq_def}  & @{thm HOL.Uniq_def}  & @{thm[show_types]HOL.Uniq_def}  \\ \hline
@{thm[source]HOL.Ex1_def}   & @{thm HOL.Ex1_def}   & @{thm[show_types]HOL.Ex1_def}   \\ \hline
\end{tabular}}\<close>}
\<^outmat>\<open>
\<^vs>\<open>0.5cm\<close>
\resizebox{\textwidth}{!}{
\begin{tabular}{|p{0.25\textwidth}|p{0.37\textwidth}|p{0.38\textwidth}|} \hline
\textbf{Name}               & \textbf{Theorem}     & \textbf{Show\_types option}     \\ \hline\hline
@{thm[source]HOL.True_def}  & @{thm HOL.True_def}  & @{thm[show_types]HOL.True_def}  \\ \hline
@{thm[source]HOL.All_def}   & @{thm HOL.All_def}   & @{thm[show_types]HOL.All_def}   \\ \hline
@{thm[source]HOL.Ex_def}    & @{thm HOL.Ex_def}    & @{thm[show_types]HOL.Ex_def}    \\ \hline
@{thm[source]HOL.False_def} & @{thm HOL.False_def} & @{thm[show_types]HOL.False_def} \\ \hline
@{thm[source]HOL.not_def}   & @{thm HOL.not_def}   & @{thm[show_types]HOL.not_def}   \\ \hline
@{thm[source]HOL.and_def}   & @{thm HOL.and_def}   & @{thm[show_types]HOL.and_def}   \\ \hline
@{thm[source]HOL.or_def}    & @{thm HOL.or_def}    & @{thm[show_types]HOL.or_def}    \\ \hline
@{thm[source]HOL.Uniq_def}  & @{thm HOL.Uniq_def}  & @{thm[show_types]HOL.Uniq_def}  \\ \hline
@{thm[source]HOL.Ex1_def}   & @{thm HOL.Ex1_def}   & @{thm[show_types]HOL.Ex1_def}   \\ \hline
\end{tabular}}
\<close>
\<close>
(*<*)
end
(*>*)