(*<*)
theory "annex"
  imports   "small_steps"
begin

(*>*)

(* text_raw\<open> \pagebreak \<close> *)
section*["laws"::technical,main_author="Some(@{author ''ben''}::author)", level=\<open>Some 3\<close>]
\<open>The Derived Rules of the Operational Semantics at a Glance\<close>


(* \<^noindent> \<^term>\<open>P \<sqinter> Q\<close>, \<^term>\<open>P \<box> Q\<close> and \<^term>\<open>P \<lbrakk>S\<rbrakk> Q\<close> are commutative so we only write the ``left-sided'' rules. *)

text(in OpSemTransitionsAll) \<open>
\begin{center}
\<^vs>\<open>0.3cm\<close>
@{thm[mode=Rule] ev_trans_\<tau>_trans} \qquad @{thm[mode=Rule] \<tau>_trans_ev_trans}

@{thm[mode=Rule] tick_trans_\<tau>_trans} \qquad @{thm[mode=Rule] \<tau>_trans_tick_trans}

\<^vs>\<open>0.25cm\<close>
{\sc absorption}
\<^vs>\<open>0.3cm\<close> \par\noindent\textcolor{lipicsLineGray}{\rule{0.8\textwidth}{1pt}} \<^vs>\<open>0.3cm\<close>

@{thm[mode=Axiom] SKIP_OpSem_rule} {\sc \<^const>\<open>SKIP\<close>}
\<^vs>\<open>0.3cm\<close> \par\noindent\textcolor{lipicsLineGray}{\rule{0.8\textwidth}{1pt}} \<^vs>\<open>0.3cm\<close>

@{thm[mode=Rule, eta_contract=false] fix_point_OpSem_rule} {\sc fixed point}
\<^vs>\<open>0.3cm\<close> \par\noindent\textcolor{lipicsLineGray}{\rule{0.8\textwidth}{1pt}} \<^vs>\<open>0.3cm\<close>


@{thm[mode=Axiom] prefix_OpSem_rules(1)} \qquad
@{thm[mode=Rule, eta_contract=false] prefix_OpSem_rules(2)} \qquad
@{thm[mode=Rule, eta_contract=false] prefix_OpSem_rules(3)}

\<^vs>\<open>0.25cm\<close>
{\sc prefix}
\<^vs>\<open>0.3cm\<close> \par\noindent\textcolor{lipicsLineGray}{\rule{0.8\textwidth}{1pt}} \<^vs>\<open>0.3cm\<close> 


@{thm[mode=Axiom] Ndet_OpSem_rules(1)} \qquad
@{thm[mode=Axiom] Ndet_OpSem_rules(2)} \qquad
@{thm[mode=Rule, eta_contract=false] Ndet_OpSem_rules(3)}

\<^vs>\<open>0.25cm\<close>
{\sc internal choice}
\<^vs>\<open>0.3cm\<close> \par\noindent\textcolor{lipicsLineGray}{\rule{0.8\textwidth}{1pt}} \<^vs>\<open>0.3cm\<close> 


@{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(1)} \qquad
@{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(3)} \qquad
@{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(5)}

@{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(2)} \qquad
@{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(4)} \qquad
@{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(6)} 

\<^vs>\<open>0.25cm\<close>
{\sc external choice}
\<^vs>\<open>0.3cm\<close> \par\noindent\textcolor{lipicsLineGray}{\rule{0.8\textwidth}{1pt}} \<^vs>\<open>0.3cm\<close>


@{thm[mode=Axiom] Sliding_OpSem_rules(1)} \qquad
@{thm[mode=Rule, eta_contract=false] Sliding_OpSem_rules(2)} \qquad
@{thm[mode=Rule, eta_contract=false] Sliding_OpSem_rules(3)} \qquad
@{thm[mode=Rule, eta_contract=false] Sliding_OpSem_rules(4)} 

\<^vs>\<open>0.25cm\<close>
{\sc sliding choice}
\<^vs>\<open>0.3cm\<close> \par\noindent\textcolor{lipicsLineGray}{\rule{0.8\textwidth}{1pt}} \<^vs>\<open>0.3cm\<close> 


@{thm[mode=Rule, eta_contract=false] Seq_OpSem_rules(1)} \qquad
@{thm[mode=Rule, eta_contract=false] Seq_OpSem_rules(2)} \qquad
@{thm[mode=Rule, eta_contract=false] Seq_OpSem_rules(3)}

\<^vs>\<open>0.25cm\<close>
{\sc sequential composition}
\<^vs>\<open>0.3cm\<close> \par\noindent\textcolor{lipicsLineGray}{\rule{0.8\textwidth}{1pt}} \<^vs>\<open>0.3cm\<close> 


@{thm[mode=Rule, eta_contract=false] Hiding_OpSem_rules(1)} \qquad
@{thm[mode=Rule, eta_contract=false] Hiding_OpSem_rules(2)}

@{thm[mode=Rule, eta_contract=false] Hiding_OpSem_rules(3)} \qquad
@{thm[mode=Rule, eta_contract=false] Hiding_OpSem_rules(4)}

\<^vs>\<open>0.25cm\<close>
{\sc hiding}
\<^vs>\<open>0.3cm\<close> \par\noindent\textcolor{lipicsLineGray}{\rule{0.8\textwidth}{1pt}} \<^vs>\<open>0.3cm\<close> 


@{thm[mode=Rule, eta_contract=false] Sync_OpSem_rules(1)} \qquad
@{thm[mode=Rule, eta_contract=false] Sync_OpSem_rules(3)} \qquad
@{thm[mode=Rule, eta_contract=false] Sync_OpSem_rules(6)}

@{thm[mode=Rule, eta_contract=false] Sync_OpSem_rules(2)} \qquad
@{thm[mode=Rule, eta_contract=false] Sync_OpSem_rules(4)} \qquad
@{thm[mode=Rule, eta_contract=false] Sync_OpSem_rules(7)}

@{thm[mode=Rule, eta_contract=false] Sync_OpSem_rules(5)} \qquad
@{thm[mode=Axiom] Sync_OpSem_rules(8)} 

\<^vs>\<open>0.25cm\<close>
{\sc synchronization}
\<^vs>\<open>0.3cm\<close> \par\noindent\textcolor{lipicsLineGray}{\rule{0.8\textwidth}{1pt}} \<^vs>\<open>0.3cm\<close> 


@{thm[mode=Rule, eta_contract=false] Interrupt_OpSem_rules(1)} \qquad
@{thm[mode=Rule, eta_contract=false] Interrupt_OpSem_rules(3)} \qquad
@{thm[mode=Rule, eta_contract=false] Interrupt_OpSem_rules(5)} 

@{thm[mode=Rule, eta_contract=false] Interrupt_OpSem_rules(2)} \qquad
@{thm[mode=Rule, eta_contract=false] Interrupt_OpSem_rules(4)} \qquad
@{thm[mode=Rule, eta_contract=false] Interrupt_OpSem_rules(6)}

\<^vs>\<open>0.25cm\<close>
{\sc interrupt}
\<^vs>\<open>0.3cm\<close> \par\noindent\textcolor{lipicsLineGray}{\rule{0.8\textwidth}{1pt}} \<^vs>\<open>0.3cm\<close> 


@{thm[mode=Rule, eta_contract=false] Throw_OpSem_rules(1)} \qquad
@{thm[mode=Rule, eta_contract=false] Throw_OpSem_rules(2)}

@{thm[mode=Rule, eta_contract=false] Throw_OpSem_rules(3)} \qquad
@{thm[mode=Rule, eta_contract=false] Throw_OpSem_rules(4)} 

\<^vs>\<open>0.25cm\<close>
{\sc throw}
\<^vs>\<open>0.3cm\<close> \par\noindent\textcolor{lipicsLineGray}{\rule{0.8\textwidth}{1pt}} \<^vs>\<open>0.3cm\<close> 

\end{center}
\<close>


text(in OpSemTransitionsAllDuplicated) \<open>\<^vs>\<open>-1.26cm\<close>
\begin{center}
@{thm[mode=Rule, eta_contract=false] Renaming_OpSem_rules(1)}

@{thm[mode=Rule, eta_contract=false] Renaming_OpSem_rules(3)} \qquad
@{thm[mode=Rule, eta_contract=false] Renaming_OpSem_rules(2)}

\<^vs>\<open>0.25cm\<close>
{\sc renaming}
\end{center}

\<close>

(*<*)

(* (* First version here *)

context OpSemTransitionsAll
begin


(*
@{thm[mode=Axiom] SKIP_OpSem_rule} \qquad 
@{thm[mode=Axiom] SKIP_cant_ev_trans} \qquad {\sc SKIP rules}
\<^vs>\<open>0.5cm\<close> \par\noindent\textcolor{lipicsLineGray}{\rule{0.8\textwidth}{1pt}} \<^vs>\<open>0.5cm\<close>


@{thm[mode=Axiom] STOP_cant_tick_trans} \qquad 
@{thm[mode=Axiom] STOP_cant_ev_trans} \qquad {\sc STOP rules}
\<^vs>\<open>0.5cm\<close> \par\noindent\textcolor{lipicsLineGray}{\rule{0.8\textwidth}{1pt}} \<^vs>\<open>0.5cm\<close>
 *)

text \<open>
Finally, by assembling the locales of each operator (which is inheriting of all these locales),
this construction led the authors to obtain the following rules (formally proven):

\begin{center}
\<^vs>\<open>0.5cm\<close>
@{thm[mode=Rule] ev_trans_\<tau>_trans} \qquad @{thm[mode=Rule] \<tau>_trans_ev_trans}

@{thm[mode=Rule] tick_trans_\<tau>_trans} \qquad @{thm[mode=Rule] \<tau>_trans_tick_trans}

{\sc absorbtion rules}
\<^vs>\<open>0.5cm\<close> \par\noindent\textcolor{lipicsLineGray}{\rule{0.8\textwidth}{1pt}} \<^vs>\<open>0.5cm\<close>


@{thm[mode=Axiom] SKIP_OpSem_rule} {\sc SKIP rule}
\<^vs>\<open>0.5cm\<close> \par\noindent\textcolor{lipicsLineGray}{\rule{0.8\textwidth}{1pt}} \<^vs>\<open>0.5cm\<close>


@{thm[mode=Axiom] prefix_OpSem_rules(1)} \qquad {\sc prefix rules}

@{thm[mode=Rule, eta_contract=false] prefix_OpSem_rules(2)} \qquad
@{thm[mode=Rule, eta_contract=false] prefix_OpSem_rules(3)}

\<^vs>\<open>0.5cm\<close> \par\noindent\textcolor{lipicsLineGray}{\rule{0.8\textwidth}{1pt}} \<^vs>\<open>0.5cm\<close> 


@{thm[mode=Axiom] Ndet_OpSem_rules(1)} \qquad
@{thm[mode=Axiom] Ndet_OpSem_rules(2)} \qquad
@{thm[mode=Rule, eta_contract=false] Ndet_OpSem_rules(3)} \qquad {\sc Ndet rules}
\<^vs>\<open>0.5cm\<close> \par\noindent\textcolor{lipicsLineGray}{\rule{0.8\textwidth}{1pt}} \<^vs>\<open>0.5cm\<close> 


@{thm[mode=Rule, eta_contract=false] fix_point_OpSem_rule} {\sc fixed point rule}
\<^vs>\<open>0.5cm\<close> \par\noindent\textcolor{lipicsLineGray}{\rule{0.8\textwidth}{1pt}} \<^vs>\<open>0.5cm\<close> 


@{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(1)} \qquad
@{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(3)} \qquad
@{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(5)}

@{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(2)} \qquad
@{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(4)} \qquad
@{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(6)} 

{\sc Det rules}
\<^vs>\<open>0.5cm\<close> \par\noindent\textcolor{lipicsLineGray}{\rule{0.8\textwidth}{1pt}} \<^vs>\<open>0.5cm\<close> 


@{thm[mode=Rule, eta_contract=false] Seq_OpSem_rules(1)} \qquad
@{thm[mode=Rule, eta_contract=false] Seq_OpSem_rules(2)} \qquad
@{thm[mode=Rule, eta_contract=false] Seq_OpSem_rules(3)} \qquad {\sc Seq rules}
\<^vs>\<open>0.5cm\<close> \par\noindent\textcolor{lipicsLineGray}{\rule{0.8\textwidth}{1pt}} \<^vs>\<open>0.5cm\<close> 


@{thm[mode=Rule, eta_contract=false] Hiding_OpSem_rules(1)} \qquad
@{thm[mode=Rule, eta_contract=false] Hiding_OpSem_rules(2)}

@{thm[mode=Rule, eta_contract=false] Hiding_OpSem_rules(3)} \qquad
@{thm[mode=Rule, eta_contract=false] Hiding_OpSem_rules(4)}

{\sc Hiding rules}
\<^vs>\<open>0.5cm\<close> \par\noindent\textcolor{lipicsLineGray}{\rule{0.8\textwidth}{1pt}} \<^vs>\<open>0.5cm\<close> 


@{thm[mode=Rule, eta_contract=false] Sync_OpSem_rules(1)} \qquad
@{thm[mode=Rule, eta_contract=false] Sync_OpSem_rules(3)} \qquad
@{thm[mode=Rule, eta_contract=false] Sync_OpSem_rules(6)}

@{thm[mode=Rule, eta_contract=false] Sync_OpSem_rules(2)} \qquad
@{thm[mode=Rule, eta_contract=false] Sync_OpSem_rules(4)} \qquad
@{thm[mode=Rule, eta_contract=false] Sync_OpSem_rules(7)}

@{thm[mode=Rule, eta_contract=false] Sync_OpSem_rules(5)} \qquad
@{thm[mode=Axiom] Sync_OpSem_rules(8)} 

{\sc Sync rules}
\<^vs>\<open>0.5cm\<close> \par\noindent\textcolor{lipicsLineGray}{\rule{0.8\textwidth}{1pt}} \<^vs>\<open>0.5cm\<close> 


@{thm[mode=Axiom] Sliding_OpSem_rules(1)} \qquad
@{thm[mode=Rule, eta_contract=false] Sliding_OpSem_rules(2)}

@{thm[mode=Rule, eta_contract=false] Sliding_OpSem_rules(3)} \qquad
@{thm[mode=Rule, eta_contract=false] Sliding_OpSem_rules(4)} 

{\sc Sliding rules}
\<^vs>\<open>0.5cm\<close> \par\noindent\textcolor{lipicsLineGray}{\rule{0.8\textwidth}{1pt}} \<^vs>\<open>0.5cm\<close> 


@{thm[mode=Rule, eta_contract=false] Interrupt_OpSem_rules(1)} \qquad
@{thm[mode=Rule, eta_contract=false] Interrupt_OpSem_rules(3)} \qquad
@{thm[mode=Rule, eta_contract=false] Interrupt_OpSem_rules(5)} 

@{thm[mode=Rule, eta_contract=false] Interrupt_OpSem_rules(2)} \qquad
@{thm[mode=Rule, eta_contract=false] Interrupt_OpSem_rules(4)} \qquad
@{thm[mode=Rule, eta_contract=false] Interrupt_OpSem_rules(6)}

{\sc Interrupt rules}
\<^vs>\<open>0.5cm\<close> \par\noindent\textcolor{lipicsLineGray}{\rule{0.8\textwidth}{1pt}} \<^vs>\<open>0.5cm\<close> 


@{thm[mode=Rule, eta_contract=false] Throw_OpSem_rules(1)} \qquad
@{thm[mode=Rule, eta_contract=false] Throw_OpSem_rules(2)}

@{thm[mode=Rule, eta_contract=false] Throw_OpSem_rules(3)} \qquad
@{thm[mode=Rule, eta_contract=false] Throw_OpSem_rules(4)} 

{\sc Throw rules}
\<^vs>\<open>0.5cm\<close> \par\noindent\textcolor{lipicsLineGray}{\rule{0.8\textwidth}{1pt}} \<^vs>\<open>0.5cm\<close> 

\end{center}
\<close>


end

context OpSemTransitionsAllDuplicated
begin


text \<open>
\begin{center}
@{thm[mode=Rule, eta_contract=false] Renaming_OpSem_rules(1)} \qquad {\sc Renaming rules}

@{thm[mode=Rule, eta_contract=false] Renaming_OpSem_rules(2)} \qquad
@{thm[mode=Rule, eta_contract=false] Renaming_OpSem_rules(3)}
\end{center}

\<close>


end

 *)

(* 


context OpSemTransitionsAll
begin


text \<open>
In the end, this construction rely on twelve \<^theory_text>\<open>locale\<close> assumptions about the \<open>\<tau>\<close> transition (that
are straightforward for FD and DT-refinements):
\begin{center}
@{thm [mode=Axiom] \<tau>_trans_NdetL} \qquad
@{thm [mode=Rule] \<tau>_trans_transitivity} \qquad
@{thm [mode=Rule] \<tau>_trans_anti_mono_initials} \qquad
@{thm [mode=Rule] \<tau>_trans_mono_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k} \qquad
@{thm [mode=Rule] \<tau>_trans_DetL} \qquad
@{thm [mode=Rule] \<tau>_trans_SeqL} \qquad
@{thm [mode=Rule] \<tau>_trans_Hiding} \qquad
@{thm [mode=Rule] \<tau>_trans_SyncL} \qquad
@{thm [mode=Rule] \<tau>_trans_SlidingL} \qquad
@{thm [mode=Rule] \<tau>_trans_InterruptR} \qquad
@{thm [mode=Rule, eta_contract=false] \<tau>_trans_ThrowL}
\end{center}\<close>


end

context OpSemTransitionsAllDuplicated
begin


text \<open>
with one additional axiom in the duplicated construction for the \<^const>\<open>Renaming\<close> operator:
\begin{center}
@{thm [mode=Rule] \<tau>_trans_Renaming}
\end{center} \<close>


end
 *)


end
(*>*) 
