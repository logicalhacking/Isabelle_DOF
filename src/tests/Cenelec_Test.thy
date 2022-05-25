theory 
  Cenelec_Test
imports 
  "Isabelle_DOF.CENELEC_50128"
begin

declare[[strict_monitor_checking = true]]
declare[[invariants_checking = true]]
declare[[invariants_checking_with_tactics = true]]

print_doc_items
print_doc_classes

open_monitor*[SIL0Test::monitor_SIL0]

text*[sqap_intance::SQAP, sil="SIL0", written_by="Some RQM", fst_check="Some VER", snd_check="Some VAL"]\<open>\<close>
text*[sqavr_intance::SQAVR, sil= "SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[scmp_intance::SCMP, sil="SIL0", written_by="Some CM", fst_check="Some VER", snd_check="Some VAL"]\<open>\<close>
text*[svp_intance::SVP, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[svap_intance::SVAP, sil="SIL0", written_by="Some VAL", fst_check="Some VER", snd_check="None"]\<open>\<close>
text*[swrs_intance::SWRS, sil="SIL0", written_by="Some RQM", fst_check="Some VER", snd_check="Some VAL"]\<open>\<close>
text*[oswts_intance::OSWTS, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swrvr_intance::SWRVR, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swas_intance::SWAS, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swds_intance::SWDS, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swis_intance::SWIS, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swits_intance::SWITS, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swhits_intance::SWHITS, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swadvr_intance::SWADVR, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swcds_intance::SWCDS, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swcts_intance::SWCTS, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swcdvr_intance::SWCDVR, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swscd_intance::SWSCD, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swctr_intance::SWCTR, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swscvr_intance::SWSCVR, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[switr_intance::SWITR, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swhaitr_intance::SWHAITR, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swivr_intance::SWIVR, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[oswtr_intance::OSWTR, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swvalr_intance::SWVALR, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[tvalr_intance::TVALR, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swvrn_intance::SWVRN, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[ars_intance::ARS, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[app_intance::APP, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[ats_intance::ATS, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[aad_intance::AAD, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[apvr_intance::APVR, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[atr_intance::ATR, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[socoada_intance::SOCOADA, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[adavr_intance::ADAVR, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swrdp_intance::SWRDP, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swdm_intance::SWDM, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swdrn_intance::SWDRN, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swdr_intance::SWDR, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swdvr_intance::SWDVR, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swmp_intance::SWMP, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swcr_intance::SWCR, sil="SIL0", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swmr_intance::SWMR, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swmvr_intance::SWMVR, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swap_intance::SWAP, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>
text*[swar_intance::SWAR, sil="SIL0", nlvl="R", written_by="Some VER", fst_check="None", snd_check="Some VAL"]\<open>\<close>

close_monitor*[SIL0Test]

declare[[strict_monitor_checking = true]]
declare[[invariants_checking = true]]
declare[[invariants_checking_with_tactics = true]]

