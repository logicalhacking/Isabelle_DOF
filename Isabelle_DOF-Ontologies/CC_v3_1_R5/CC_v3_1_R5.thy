(*************************************************************************
 * Copyright (C) 
 *               2019-2022 The University of Exeter 
 *               2019-2022 The University of Paris-Saclay
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

section\<open>CC 3.1.R5\<close>
(*<*)
theory  "CC_v3_1_R5"
  imports 
 "Isabelle_DOF.technical_report" 
           "CC_terminology"


begin
(*>*)

subsection \<open>General Infrastructure on CC Evaluations\<close>

datatype EALs = EAL1 |  EAL2 |  EAL3 |  EAL4 |  EAL5 |  EAL6 | EAL7

doc_class CC_structure_element =(* text_element + *)
          tag_id :: string
          eval_level :: EALs

doc_class CC_text_element = text_element +
          eval_level :: EALs

subsection \<open>Security target ontology\<close>


doc_class st_ref_cls = CC_text_element +
    title    :: string
    st_version:: "(int \<times> int \<times> int)"
    "authors":: "author list"
    "st_date"   :: string

doc_class toe_ref_cls = CC_text_element +
    dev_name:: string
    toe_name:: string
    toe_version:: "(int \<times> int \<times> int)"
    prod_name::"string option" <= None


doc_class toe_ovrw_cls = CC_text_element +
    toe_type     :: string
    software_req :: "CC_text_element list" <= "[]"
    hardware_req :: "CC_text_element list" <= "[]" 
    firmeware_req:: "CC_text_element list" <= "[]"
    features_req :: "CC_text_element list" <= "[]"
    invariant  eal_consistency:: 
                 "(case eval_level \<sigma>  of 
                           EAL1 \<Rightarrow> software_req  \<sigma> \<noteq> [] 
                      |    EAL2 \<Rightarrow> software_req  \<sigma> \<noteq> [] 
                      |    EAL3 \<Rightarrow> software_req  \<sigma> \<noteq> [] 
                      |    EAL4 \<Rightarrow> software_req  \<sigma> \<noteq> [] 
                      |    _ \<Rightarrow>  undefined)"

thm eal_consistency_inv_def

doc_class toe_desc_cls = CC_text_element +
    software_list    :: "CC_text_element list" <= "[]"
    hardware_list    :: "CC_text_element list" <= "[]" 
    firmeware_list   :: "CC_text_element list" <= "[]"
    sec_features_list:: "CC_text_element list" <= "[]"
  
doc_class ST_INTRO_MNT = CC_structure_element +
    tag_id:: string
    accepts "\<lbrace>st_ref_cls\<rbrace>\<^sup>* ~~ \<lbrace>toe_ref_cls\<rbrace>\<^sup>* ~~ \<lbrace>toe_ovrw_cls\<rbrace>\<^sup>* ~~ \<lbrace>toe_desc_cls\<rbrace>\<^sup>*"

doc_class cc_conf_claim_cls = CC_text_element +
    cc_version:: string
    ext_srs_list::"CC_text_element list option"
   
doc_class pp_clms_cls = CC_text_element +
    pp_pckgs_list::"CC_text_element list option"
    pp_config_list::"CC_text_element list option"

doc_class pckg_claim_cls = CC_text_element +
    pckgs_list::"CC_text_element list option"

doc_class conf_ratio =
    pp_config_list::"CC_text_element list option"

doc_class CONF_CLAIMS_MNT = CC_structure_element +
    tag_id:: string
    accepts "(\<lbrace>cc_conf_claim_cls\<rbrace>\<^sup>+ ~~ \<lbrace>pp_clms_cls\<rbrace>\<^sup>* ~~ \<lbrace>pckg_claim_cls\<rbrace>\<^sup>+ ~~ \<lbrace>conf_ratio\<rbrace>\<^sup>*)"
 
doc_class threats_cls = CC_text_element +
    toe_thrts_list::"CC_text_element list option"
    env_thrts_list::"CC_text_element list option"
    thrt_agnts_list:: "CC_text_element list option"
    advrt_acts_list:: "CC_text_element list option"
    assts_list:: "CC_text_element list option"

doc_class osps_cls = CC_text_element +
    toe_osps_list::"CC_text_element list option"
    env_osps_list::"CC_text_element list option"

doc_class assumptions_cls = CC_text_element +
    assms_phy_list::"CC_text_element list option"
    assms_prsnl_list::"CC_text_element list option"
    assms_cnct_list::"CC_text_element list option"

doc_class SEC_PROB_DEF_MNT = CC_structure_element +
  tag_id:: string
  accepts "((\<lbrace>threats_cls\<rbrace>\<^sup>+ || \<lbrace>osps_cls\<rbrace>\<^sup>+) ~~ \<lbrace>assumptions_cls\<rbrace>\<^sup>+)"

doc_class toe_sec_obj_cls = CC_text_element +
  toe_obj_list:: "CC_text_element list"

doc_class env_sec_obj_cls = CC_text_element +
  env_goals_list:: "CC_text_element list"
  env_sites_list :: "CC_text_element list"

doc_class sec_obj_ratio =
  toe_thrts_obj_trace::"((threats_cls \<times> toe_sec_obj_cls) list) option"
  toe_osps_obj_trace::"((osps_cls \<times> toe_sec_obj_cls) list) option"
  toe_assms_obj_trace::"((assumptions_cls \<times> toe_sec_obj_cls) list) option"
  env_thrts_obj_trace::"((threats_cls \<times> toe_sec_obj_cls) list) option"
  env_osps_obj_trace::"((osps_cls \<times> toe_sec_obj_cls) list) option"
  env_assms_obj_trace::"((assumptions_cls \<times> toe_sec_obj_cls) list) option"
  toe_thrts_just_list::"(CC_text_element list) option"
  toe_osps_just_list::"(CC_text_element list) option"
  toe_assms_just_list::"CC_text_element list"
  env_thrts_just_list::"(CC_text_element list) option"
  env_osps_just_list::"(CC_text_element list) option"
  env_assms_just_list::"CC_text_element list"

doc_class ext_comp_def =
  ext_comp_list::"(CC_text_element list) option"

doc_class SEC_OBJ_MNT = CC_structure_element +
  tag_id:: string
  accepts "(\<lbrace>toe_sec_obj_cls\<rbrace>\<^sup>+ ~~ \<lbrace>env_sec_obj_cls\<rbrace>\<^sup>+ ~~ \<lbrace>sec_obj_ratio\<rbrace>\<^sup>*~~ \<lbrace>ext_comp_def\<rbrace>\<^sup>*)"


doc_class sfrs_cls = CC_text_element +
  sfrs_language::"string"
  sfrs_operation::"CC_text_element"
  sfrs_dependency::"CC_text_element list option"

doc_class sfrs_ratio_cls = CC_text_element +
  toe_sec_obj_sfrs_trace:: "(sfrs_cls \<times> toe_sec_obj_cls) list"
  toe_sec_obj_sfrs_just::"CC_text_element list option"

doc_class sars_cls = CC_text_element +
  sars_language::"string"
  sars_operation::"CC_text_element"
  sars_dependency::"CC_text_element list option"

doc_class sars_ratio_cls = CC_text_element +
  sars_explain::"CC_text_element list"

doc_class SEC_REQ_MNT =
  spd_id:: string
  accepts "(\<lbrace>sfrs_cls\<rbrace>\<^sup>+ ~~ \<lbrace>sfrs_ratio_cls\<rbrace>\<^sup>+ ~~ \<lbrace>sars_cls\<rbrace>\<^sup>+ ~~ \<lbrace>sars_ratio_cls\<rbrace>\<^sup>+)"

doc_class ST_MNT = CC_structure_element +
   tag_id :: string
   level :: EALs
   accepts "(ST_INTRO_MNT  ~~
             CONF_CLAIMS_MNT ~~
             SEC_PROB_DEF_MNT ~~
             SEC_OBJ_MNT ~~
             SEC_REQ_MNT)"


end
