(*<*)
theory "05_IsaDofLaTeX"
  imports "04_RefMan"
begin
(*>*)

chapter*[latex::technical,main_author="Some(@{docitem ''adb''}::author)"]\<open> PDF Generation with \isadof \<close>


section*[latex1::technical]\<open>How to adapt \isadof to a new document style file\<close>

text\<open>Current \isadof comes with a number of setups for the PDF generation, notably
Springer LNCS, lipics, ..., as well as setupqs of technical reports this the present one.

The question arises, what to do if \isadof has to be accoustomed to a new LaTeX style
file configuration in order to generate PDF.
\<close>
text\<open> 
In theory, this is simple - in practice, the efforts required
depends mostly on two factors:

\<^item> how compatible is the required LaTeX class with Isabelle's LateX 
 setup in general (e.g., does it work with an antique version 
 of \<open>comment.sty\<close> required by Isabelle)

\<^item>  how much magic does the required LaTeX class wrt the title page
 information (author, affiliation). 

\<^item>  which ontologies should be supported. While most ontologies are 
 generic, some only support a very specific subset of LaTeX 
 templates (classes).  For example, \<^theory_text>\<open>scholarly_paper\<close> does currently 
 \<^emph>\<open>only\<close> support \<open>llncs\<close>, \<open>rartcl\<close>, and \<open>lipics\<close>. 

The general process as such is straight-forward:

\<^enum> From the supported LaTeX classes, try to find the one that is 
  most similar to the one that you want to support. For the sake
  of the this example, let's assume this is llncs
\<^enum> Use the template for this class (llncs) as starting point, i.e.,
  \<^verbatim>\<open>cp document-generator/document-template/root-lncs.tex 
   document-generator/document-template/root-eptcs.tex\<close>

  The mandatory naming scheme for the templates is 

      \<^verbatim>\<open>root-<TEMPLATE_NAME>.tex\<close>

  That is to say that \<^verbatim>\<open><TEMPLATE_NAME>\<close> should be the name of the
  new LaTeX class (all lowercase preferred) that will be used
  in config files and also will be shown in the help text
  shown by executing 

      \<^verbatim>\<open>isabelle DOF_mkroot -h\<close>

\<^enum> Edit the new template as necessary (using the provided 
  example from the target class as reference):

     \<^verbatim>\<open>vim document-generator/document-template/root-foo.tex\<close>

  and do the needful.

\<^enum> Install the new template:

     \<^verbatim>\<open>./install\<close>

  (If you have a working installation of the required AFP entries
   and the Isabelle/DOF patch, you can use \<^verbatim>\<open>./install -s\<close>
   which will \<^emph>\<open>ONLY\<close> install the \<^verbatim>\<open>LaTeX styles/templates\<close>, see 
   \<^verbatim>\<open>./install -h)\<close>

\<^enum> Now the new template should be available, you can check this  with 
 
     \<^verbatim>\<open>isabelle DOF_mkroot -h\<close>

\<^enum> Create an "tiny/empty" Isabelle project using the ontology "core"
  and test your template. If everything works, celebrate. If it does 
  not work, understand what you need to change and continue 
  with step 3. 

  (of course, if the new class is not available in TeXLive, you need
  to add them locally to the documents folder of your Isabelle 
  project and, as usual, it needs to be registered in your ROOTS
  file)

\<^enum> If the ontologies that should be used together with this LaTeX
  class do not require specific adaptions (e.g., CENELEC 50128), 
  everything should work. If one of the required ontology LaTeX
  setups only supports a subset of LaTeX classes (e.g., \<^theory_text>\<open>scholarly_paper\<close> 
  due to the different setups for authors/affiliations blurb), 
  you need to develop support for you new class in the ontology 
  specific LaTeX styles, e.g., 
  \<open>document-generator/latex/DOF-scholarly_paper.sty\<close>
  (mandatory naming convention: \<open>DOF-<ONTOLOGY_NAME>.sty\<close>)

\<^enum> After updating the ontology style (or styles), you need 
  to install them (again, you might want to use ./install -s)
  and test your setup with a paper configuration using 
  your new LaTeX template and the required styles. In case
  of errors, go back to step 7.

\<close>



(*<*)
end
(*>*) 
  
