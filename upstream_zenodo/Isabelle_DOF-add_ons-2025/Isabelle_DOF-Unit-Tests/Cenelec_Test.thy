theory 
  Cenelec_Test
imports 
  "Isabelle_DOF_Unit_Tests_document"
  "Isabelle_DOF-Ontologies.CENELEC_50128"
begin

declare[[strict_monitor_checking = true]]
declare[[invariants_checking = true]]
declare[[invariants_checking_with_tactics = true]]

print_doc_items
print_doc_classes

open_monitor*[SIL0Test::monitor_SIL0]

text*[sqap_instance::SQAP, sil="SIL0", written_by="Some RQM", fst_check="Some VER", snd_check="Some VAL"]\<open>\<close>
text*[sqavr_instance::SQAVR, sil= "SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[scmp_instance::SCMP, sil="SIL0", written_by="Some CM", fst_check="Some VER", snd_check="Some VAL"]\<open>\<close>
text*[svp_instance::SVP, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[svap_instance::SVAP, sil="SIL0", written_by="Some VAL", fst_check="Some VER", snd_check="None"]\<open>\<close>
text*[swrs_instance::SWRS, sil="SIL0", written_by="Some RQM", fst_check="Some VER", snd_check="Some VAL"]\<open>\<close>
text*[oswts_instance::OSWTS, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swrvr_instance::SWRVR, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swas_instance::SWAS, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swds_instance::SWDS, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swis_instance::SWIS, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swits_instance::SWITS, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swhits_instance::SWHITS, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swadvr_instance::SWADVR, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swcds_instance::SWCDS, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swcts_instance::SWCTS, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swcdvr_instance::SWCDVR, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swscd_instance::SWSCD, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swctr_instance::SWCTR, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swscvr_instance::SWSCVR, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[switr_instance::SWITR, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swhaitr_instance::SWHAITR, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swivr_instance::SWIVR, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[oswtr_instance::OSWTR, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swvalr_instance::SWVALR, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[tvalr_instance::TVALR, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swvrn_instance::SWVRN, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[ars_instance::ARS, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[app_instance::APP, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[ats_instance::ATS, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[aad_instance::AAD, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[apvr_instance::APVR, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[atr_instance::ATR, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[socoada_instance::SOCOADA, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[adavr_instance::ADAVR, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swrdp_instance::SWRDP, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swdm_instance::SWDM, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swdrn_instance::SWDRN, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swdr_instance::SWDR, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swdvr_instance::SWDVR, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swmp_instance::SWMP, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swcr_instance::SWCR, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swmr_instance::SWMR, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swmvr_instance::SWMVR, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swap_instance::SWAP, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swar_instance::SWAR, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>

close_monitor*[SIL0Test]

declare[[strict_monitor_checking = true]]
declare[[invariants_checking = true]]
declare[[invariants_checking_with_tactics = true]]

end 