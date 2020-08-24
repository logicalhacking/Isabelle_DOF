(* *************************************************************************
 * Copyright (C)
 *               2020      The University of Sheffield
 *               2019      The University of Exeter
 *               2018-2019 The University of Paris-Saclay
 *
 * Authors : Yakoub Nemouchi
 *           Burhart Wolff
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

theory  CommonCriteria_15408
  imports  "../technical_report/technical_report" 
           "CC_terminology"


begin
section \<open>Security target ontology\<close>


doc_class st_ref_cls = text_element +
  title    :: string
  st_version:: "(int \<times> int \<times> int)"
  "authors":: "author list"
  "st_date"   :: string

doc_class toe_ref_cls = text_element +
    dev_name:: string
    toe_name:: string
    toe_version:: "(int \<times> int \<times> int)"
    prod_name::"string option" <= None

doc_class toe_ovrw_cls = text_element +
  toe_type     :: string
  software_req :: "text_element list option" <= None
  hardware_req :: "text_element list option" <= None 
  firmeware_req:: "text_element list option" <= None
  features_req :: "text_element list option" <= None

doc_class toe_desc_cls = text_element +
  software_list :: "text_element list option" <= None
  hardware_list :: "text_element list option" <= None 
  firmeware_list:: "text_element list option" <= None
  sec_features_list:: "text_element list option" <= None
  
doc_class ST_INTRO_MNT =
  stint_id:: string
  accepts "(\<lbrace>st_ref_cls\<rbrace>\<^sup>+ ~~ \<lbrace>toe_ref_cls\<rbrace>\<^sup>+ ~~ \<lbrace>toe_ovrw_cls\<rbrace>\<^sup>+ ~~ \<lbrace>toe_desc_cls\<rbrace>\<^sup>+)"

doc_class cc_conf_claim_cls = text_element +
  cc_version:: string
  ext_srs_list::"text_element list option"
   
doc_class pp_clms_cls = text_element +
  pp_pckgs_list::"text_element list option"
  pp_config_list::"text_element list option"

doc_class pckg_claim_cls = text_element +
  pckgs_list::"text_element list option"

doc_class conf_ratio =
 pp_config_list::"text_element list option"

doc_class CONF_CLAIMS_MNT =
  ccl_id:: string
  accepts "(\<lbrace>cc_conf_claim_cls\<rbrace>\<^sup>+ ~~ \<lbrace>pp_clms_cls\<rbrace>\<^sup>* ~~ \<lbrace>pckg_claim_cls\<rbrace>\<^sup>+ ~~ \<lbrace>conf_ratio\<rbrace>\<^sup>*)"
 
doc_class threats_cls = text_element +
  toe_thrts_list::"text_element list option"
  env_thrts_list::"text_element list option"
  thrt_agnts_list:: "text_element list option"
  advrt_acts_list:: "text_element list option"
  assts_list:: "text_element list option"

doc_class osps_cls = text_element +
  toe_osps_list::"text_element list option"
  env_osps_list::"text_element list option"

doc_class assumptions_cls = text_element +
  assms_phy_list::"text_element list option"
  assms_prsnl_list::"text_element list option"
  assms_cnct_list::"text_element list option"

doc_class SEC_PROB_DEF_MNT =
  spd_id:: string
  accepts "((\<lbrace>threats_cls\<rbrace>\<^sup>+ || \<lbrace>osps_cls\<rbrace>\<^sup>+) ~~ \<lbrace>assumptions_cls\<rbrace>\<^sup>+)"

doc_class toe_sec_obj_cls = text_element +
  toe_obj_list:: "text_element list"

doc_class env_sec_obj_cls = text_element +
  env_goals_list:: "text_element list"
  env_sites_list :: "text_element list"

doc_class sec_obj_ratio =
  toe_thrts_obj_trace::"((threats_cls \<times> toe_sec_obj_cls) list) option"
  toe_osps_obj_trace::"((osps_cls \<times> toe_sec_obj_cls) list) option"
  toe_assms_obj_trace::"((assumptions_cls \<times> toe_sec_obj_cls) list) option"
  env_thrts_obj_trace::"((threats_cls \<times> toe_sec_obj_cls) list) option"
  env_osps_obj_trace::"((osps_cls \<times> toe_sec_obj_cls) list) option"
  env_assms_obj_trace::"((assumptions_cls \<times> toe_sec_obj_cls) list) option"
  toe_thrts_just_list::"(text_element list) option"
  toe_osps_just_list::"(text_element list) option"
  toe_assms_just_list::"text_element list"
  env_thrts_just_list::"(text_element list) option"
  env_osps_just_list::"(text_element list) option"
  env_assms_just_list::"text_element list"

doc_class ext_comp_def =
  ext_comp_list::"(text_element list) option"

doc_class SEC_OBJ_MNT =
  ccl_id:: string
  accepts "(\<lbrace>toe_sec_obj_cls\<rbrace>\<^sup>+ ~~ \<lbrace>env_sec_obj_cls\<rbrace>\<^sup>+ ~~ \<lbrace>sec_obj_ratio\<rbrace>\<^sup>*~~ \<lbrace>ext_comp_def\<rbrace>\<^sup>*)"


doc_class sfrs_cls = text_element +
  sfrs_language::"string"
  sfrs_operation::"text_element"
  sfrs_dependency::"text_element list option"

doc_class sfrs_ratio_cls = text_element +
  toe_sec_obj_sfrs_trace:: "(sfrs_cls \<times> toe_sec_obj_cls) list"
  toe_sec_obj_sfrs_just::"text_element list option"

doc_class sars_cls = text_element +
  sars_language::"string"
  sars_operation::"text_element"
  sars_dependency::"text_element list option"

doc_class sars_ratio_cls = text_element +
  sars_explain::"text_element list"

doc_class SEC_REQ_MNT =
  spd_id:: string
  accepts "(\<lbrace>sfrs_cls\<rbrace>\<^sup>+ ~~ \<lbrace>sfrs_ratio_cls\<rbrace>\<^sup>+ ~~ \<lbrace>sars_cls\<rbrace>\<^sup>+ ~~ \<lbrace>sars_ratio_cls\<rbrace>\<^sup>+)"

doc_class ST_MNT = 
   st_id :: string              
   accepts "(ST_INTRO_MNT  ~~
             CONF_CLAIMS_MNT ~~
             SEC_PROB_DEF_MNT ~~
             SEC_OBJ_MNT ~~
             SEC_REQ_MNT)"


end
