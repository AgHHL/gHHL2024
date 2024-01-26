theory BigStepInterruptParallel
  imports BigStepContParallel 
begin


lemma rdy_of_comm_specg2_prop1:
 assumes "i < length specs"
     and "specs ! i = InSpecg2 ch P"
   shows "ch \<in> snd (rdy_of_comm_specg2 specs)"
  using assms
  proof(induction "length specs" arbitrary: specs i)
    case 0
    then show ?case by auto
  next
    case (Suc x)
    show ?case 
      apply(cases specs)
      subgoal using Suc by auto
      subgoal for s specs'
        using Suc(2,3,4) unfolding rdy_of_comm_specg2_def
        apply auto
        apply(cases s)
        subgoal for chh PP
          apply auto
          apply(cases i)
          subgoal apply auto by (metis insertI1 snd_conv)
          subgoal for i' apply auto
            using Suc(1)[of specs' i'] unfolding rdy_of_comm_specg2_def
            apply auto
            by (smt (z3) insertI2 old.prod.inject prod.collapse rdy_of_comm_specg2_def)
          done
        subgoal for chh PP
          apply auto
          apply(cases i)
          subgoal apply auto done
          subgoal for i' apply auto
            using Suc(1)[of specs' i'] unfolding rdy_of_comm_specg2_def
            apply auto
            by (smt (z3) insertI2 old.prod.inject prod.collapse rdy_of_comm_specg2_def)
          done
        done
      done
  qed
  
lemma rdy_of_comm_specg2_prop2:
 assumes "i < length specs"
     and "specs ! i = OutSpecg2 ch P"
   shows "ch \<in> fst (rdy_of_comm_specg2 specs)"
  using assms
  proof(induction "length specs" arbitrary: specs i)
    case 0
    then show ?case by auto
  next
    case (Suc x)
    show ?case 
      apply(cases specs)
      subgoal using Suc by auto
      subgoal for s specs'
        using Suc(2,3,4) unfolding rdy_of_comm_specg2_def
        apply auto
        apply(cases s)
        subgoal for chh PP
          apply auto
          apply(cases i)
          subgoal apply auto done
          subgoal for i' apply auto
            using Suc(1)[of specs' i'] unfolding rdy_of_comm_specg2_def
            apply auto
            by (smt (z3) insertI2 old.prod.inject prod.collapse rdy_of_comm_specg2_def)
          done
        subgoal for chh PP
          apply auto
          apply(cases i)
          subgoal apply auto by (metis fst_conv insertI1)
          subgoal for i' apply auto
            using Suc(1)[of specs' i'] unfolding rdy_of_comm_specg2_def
            apply auto
            by (smt (z3) insertI2 old.prod.inject prod.collapse rdy_of_comm_specg2_def)
          done
        done
      done
  qed
                                  
fun comm_specg2_in_chs:: "'a comm_specg2 list \<Rightarrow> cname set \<Rightarrow> 'a comm_specg2 list" where
  "comm_specg2_in_chs [] chs = []"
| "comm_specg2_in_chs ((InSpecg2 ch P)#l) chs = 
    (if ch \<in> chs then (InSpecg2 ch P)#(comm_specg2_in_chs l chs) else (comm_specg2_in_chs l chs))"
| "comm_specg2_in_chs ((OutSpecg2 ch P)#l) chs = 
    (if ch \<in> chs then (OutSpecg2 ch P)#(comm_specg2_in_chs l chs) else (comm_specg2_in_chs l chs))"

fun comm_specg2_notin_chs:: "'a comm_specg2 list \<Rightarrow> cname set \<Rightarrow> 'a comm_specg2 list" where
  "comm_specg2_notin_chs [] chs = []"
| "comm_specg2_notin_chs ((InSpecg2 ch P)#l) chs = 
    (if ch \<notin> chs then (InSpecg2 ch P)#(comm_specg2_notin_chs l chs) else (comm_specg2_notin_chs l chs))"
| "comm_specg2_notin_chs ((OutSpecg2 ch P)#l) chs = 
    (if ch \<notin> chs then (OutSpecg2 ch P)#(comm_specg2_notin_chs l chs) else (comm_specg2_notin_chs l chs))"

lemma comm_specg2_notin_chs_prop1:
 assumes "i < length specs"
     and "specs ! i = InSpecg2 ch P"
     and "ch \<notin> chs"
   shows "\<exists> j. (comm_specg2_notin_chs specs chs) ! j = InSpecg2 ch P \<and> j < length (comm_specg2_notin_chs specs chs)"
  using assms 
proof(induction "length specs" arbitrary: i specs)
  case 0
  then show ?case by auto
next
  case (Suc x)
  then show ?case 
    apply(cases specs)
    subgoal by auto
    subgoal for s specs'
      apply auto
      apply(cases i)
      subgoal apply auto
        apply(rule exI[where x=0]) by auto
      subgoal for i'
        apply auto
        apply (cases s)
        subgoal for chh PP
          apply(cases "chh\<in>chs")
          subgoal by auto
          subgoal apply auto
            by (metis Suc_mono nth_Cons_Suc)
          done
        subgoal for chh PP
          apply(cases "chh\<in>chs")
          subgoal by auto
          subgoal apply auto
            by (metis Suc_mono nth_Cons_Suc)
          done
        done
      done
    done
qed

lemma comm_specg2_notin_chs_prop2:
 assumes "i < length specs"
     and "specs ! i = OutSpecg2 ch P"
     and "ch \<notin> chs"
   shows "\<exists> j. (comm_specg2_notin_chs specs chs) ! j = OutSpecg2 ch P \<and> j < length (comm_specg2_notin_chs specs chs)"
  using assms 
proof(induction "length specs" arbitrary: i specs)
  case 0
  then show ?case by auto
next
  case (Suc x)
  then show ?case 
    apply(cases specs)
    subgoal by auto
    subgoal for s specs'
      apply auto
      apply(cases i)
      subgoal apply auto
        apply(rule exI[where x=0]) by auto
      subgoal for i'
        apply auto
        apply (cases s)
        subgoal for chh PP
          apply(cases "chh\<in>chs")
          subgoal by auto
          subgoal apply auto
            by (metis Suc_mono nth_Cons_Suc)
          done
        subgoal for chh PP
          apply(cases "chh\<in>chs")
          subgoal by auto
          subgoal apply auto
            by (metis Suc_mono nth_Cons_Suc)
          done
        done
      done
    done
qed

fun ii1:: "cname set \<Rightarrow> pname set \<Rightarrow> pname set \<Rightarrow> 'a gpinv2 \<Rightarrow> 'a comm_specg2 list \<Rightarrow> 'a comm_specg2 \<Rightarrow> 'a comm_specg2" where
  "ii1 chs pns1 pns2 I specs (InSpecg2 ch P) 
     = (InSpecg2 ch (\<lambda> d v. sync_gassn chs pns1 pns2 (P d v) 
                      (interrupt_solInf_cg (delay_inv d I) (map (spec_wait_of d) specs))))"
| "ii1 chs pns1 pns2 I specs (OutSpecg2 ch P) 
     = (OutSpecg2 ch (\<lambda> d v. sync_gassn chs pns1 pns2 (P d v) 
                      (interrupt_solInf_cg (delay_inv d I) (map (spec_wait_of d) specs))))"

fun ii2:: "cname set \<Rightarrow> pname set \<Rightarrow> pname set \<Rightarrow> 'a gpinv2 \<Rightarrow> 'a comm_specg2 list \<Rightarrow> 'a comm_specg2 \<Rightarrow> 'a comm_specg2" where
  "ii2 chs pns1 pns2 I specs (InSpecg2 ch P) 
     = (InSpecg2 ch (\<lambda> d v. sync_gassn chs pns1 pns2  
                      (interrupt_solInf_cg (delay_inv d I) (map (spec_wait_of d) specs)) (P d v)))"
| "ii2 chs pns1 pns2 I specs (OutSpecg2 ch P) 
     = (OutSpecg2 ch (\<lambda> d v. sync_gassn chs pns1 pns2  
                      (interrupt_solInf_cg (delay_inv d I) (map (spec_wait_of d) specs)) (P d v)))"

lemma map_prop1[simp]:"k < length a \<Longrightarrow> ((map f a) @ (map g b)) ! k = f (a ! k)"
  by (simp add: nth_append)

lemma map_prop2[simp]:"k < length b \<Longrightarrow> ((map f a) @ (map g b)) ! (k + length a) = g (b ! k)"
  by (simp add: nth_append)

lemma rdy_of_ii:"rdy_of_comm_specg2 ((map (ii1 chs pns1 pns2 I1 specs1) L1)@  
                                          (map (ii2 chs pns3 pns4 I2 specs2) L2)) = 
                    rdy_of_comm_specg2 (L1 @ L2)"
proof(induction "length L1 + length L2"  arbitrary: L1 L2 rule: less_induct)
  case less
  show ?case 
    apply(cases L1)
    subgoal
      apply(cases L2)
      subgoal by auto
      subgoal for a2 l2
        apply(cases a2)
        subgoal 
          using less[of "[]" l2]
          by(auto simp add: rdy_of_comm_specg2_def)  
        subgoal 
          using less[of "[]" l2]
          by(auto simp add: rdy_of_comm_specg2_def)
        done
      done
    subgoal for a1 l1
      apply auto
      apply(cases a1)
      subgoal
        using less[of l1 L2]
        by(auto simp add: rdy_of_comm_specg2_def)
      subgoal
        using less[of l1 L2]
        by(auto simp add: rdy_of_comm_specg2_def)
      done
    done
qed
                         

lemma merge_rdy_of_comm_specg2_prop:"merge_rdy chs (rdy_of_comm_specg2 specs1) (rdy_of_comm_specg2 specs2) = 
                      rdy_of_comm_specg2 ((comm_specg2_notin_chs specs1 chs)@  
                                          (comm_specg2_notin_chs specs2 chs))"
proof(induction "length specs1 + length specs2"  arbitrary: specs1 specs2 rule: less_induct)
  case less
  show ?case 
    apply(cases specs1)
    subgoal 
      apply(cases specs2)
      subgoal
        apply(auto simp add: rdy_of_comm_specg2_def)
        done
      subgoal for a2 l2
        apply(cases a2)
        subgoal for ch2 P2
          using less[of "[]" l2]
          apply(auto simp add: rdy_of_comm_specg2_def)
           apply(cases "(rdy_info_of_list (case_comm_specg2 (\<lambda>ch P. ({}, {ch})) (\<lambda>ch P. ({ch}, {}))) l2)")
          apply(cases "rdy_info_of_list (case_comm_specg2 (\<lambda>ch P. ({}, {ch})) (\<lambda>ch P. ({ch}, {})))
                   (comm_specg2_notin_chs l2 chs)")
           apply auto
          apply(cases "(rdy_info_of_list (case_comm_specg2 (\<lambda>ch P. ({}, {ch})) (\<lambda>ch P. ({ch}, {}))) l2)")
          apply(cases "rdy_info_of_list (case_comm_specg2 (\<lambda>ch P. ({}, {ch})) (\<lambda>ch P. ({ch}, {})))
                   (comm_specg2_notin_chs l2 chs)")
          apply auto
          done
        subgoal for ch2 P2
          using less[of "[]" l2]
          apply(auto simp add: rdy_of_comm_specg2_def)
           apply(cases "(rdy_info_of_list (case_comm_specg2 (\<lambda>ch P. ({}, {ch})) (\<lambda>ch P. ({ch}, {}))) l2)")
          apply(cases "rdy_info_of_list (case_comm_specg2 (\<lambda>ch P. ({}, {ch})) (\<lambda>ch P. ({ch}, {})))
                    (comm_specg2_notin_chs l2 chs)")
           apply auto
          apply(cases "(rdy_info_of_list (case_comm_specg2 (\<lambda>ch P. ({}, {ch})) (\<lambda>ch P. ({ch}, {}))) l2)")
          apply(cases "rdy_info_of_list (case_comm_specg2 (\<lambda>ch P. ({}, {ch})) (\<lambda>ch P. ({ch}, {})))
                    (comm_specg2_notin_chs l2 chs)")
          apply auto
          done
        done
      done
    subgoal for a1 l1
      apply(auto simp add: rdy_of_comm_specg2_def)
      apply(cases a1)
      subgoal for ch1 P1
        using less[of l1 specs2]
        apply(auto simp add: rdy_of_comm_specg2_def)
        subgoal
          apply(cases "(rdy_info_of_list (case_comm_specg2 (\<lambda>ch P. ({}, {ch})) (\<lambda>ch P. ({ch}, {}))) l1)")
          apply(cases "(rdy_info_of_list (case_comm_specg2 (\<lambda>ch P. ({}, {ch})) (\<lambda>ch P. ({ch}, {}))) specs2)")
          apply(cases "rdy_info_of_list (case_comm_specg2 (\<lambda>ch P. ({}, {ch})) (\<lambda>ch P. ({ch}, {})))
        (comm_specg2_notin_chs l1 chs @ comm_specg2_notin_chs specs2 chs)")
          by auto
        subgoal
          apply(cases "(rdy_info_of_list (case_comm_specg2 (\<lambda>ch P. ({}, {ch})) (\<lambda>ch P. ({ch}, {}))) l1)")
          apply(cases "(rdy_info_of_list (case_comm_specg2 (\<lambda>ch P. ({}, {ch})) (\<lambda>ch P. ({ch}, {}))) specs2)")
          apply(cases "rdy_info_of_list (case_comm_specg2 (\<lambda>ch P. ({}, {ch})) (\<lambda>ch P. ({ch}, {})))
        (comm_specg2_notin_chs l1 chs @ comm_specg2_notin_chs specs2 chs)")
          by auto
        done
      subgoal for ch1 P1
        using less[of l1 specs2]
        apply(auto simp add: rdy_of_comm_specg2_def)
        subgoal
          apply(cases "(rdy_info_of_list (case_comm_specg2 (\<lambda>ch P. ({}, {ch})) (\<lambda>ch P. ({ch}, {}))) l1)")
          apply(cases "(rdy_info_of_list (case_comm_specg2 (\<lambda>ch P. ({}, {ch})) (\<lambda>ch P. ({ch}, {}))) specs2)")
          apply(cases "rdy_info_of_list (case_comm_specg2 (\<lambda>ch P. ({}, {ch})) (\<lambda>ch P. ({ch}, {})))
        (comm_specg2_notin_chs l1 chs @ comm_specg2_notin_chs specs2 chs)")
          by auto
        subgoal
          apply(cases "(rdy_info_of_list (case_comm_specg2 (\<lambda>ch P. ({}, {ch})) (\<lambda>ch P. ({ch}, {}))) l1)")
          apply(cases "(rdy_info_of_list (case_comm_specg2 (\<lambda>ch P. ({}, {ch})) (\<lambda>ch P. ({ch}, {}))) specs2)")
          apply(cases "rdy_info_of_list (case_comm_specg2 (\<lambda>ch P. ({}, {ch})) (\<lambda>ch P. ({ch}, {})))
        (comm_specg2_notin_chs l1 chs @ comm_specg2_notin_chs specs2 chs)")
          by auto
        done
      done
    done
qed
  
lemma merge_rdy_of_comm_specg2_prop':"merge_rdy chs (rdy_of_comm_specg2 specs1) (rdy_of_comm_specg2 specs2) = 
                      rdy_of_comm_specg2 ((map (ii1 chs pns1 pns2 I2 specs2) (comm_specg2_notin_chs specs1 chs))@  
                                          (map (ii2 chs pns1 pns2 I1 specs1) (comm_specg2_notin_chs specs2 chs)))"
  apply(subst rdy_of_ii[of chs pns1 pns2 I2 specs2 "(comm_specg2_notin_chs specs1 chs)" pns1 pns2 I1 specs1 "(comm_specg2_notin_chs specs2 chs)"])
  by(rule merge_rdy_of_comm_specg2_prop)


lemma sync_gassn_interrupt_solInf_interrupt_solInf1:
  assumes "compat_rdy (rdy_of_comm_specg2 specs1) (rdy_of_comm_specg2 specs2)"
shows
  "sync_gassn chs pns1 pns2 (interrupt_solInf_cg I1 specs1) (interrupt_solInf_cg I2 specs2) s0 \<Longrightarrow>\<^sub>G
   interrupt_solInf_cg (merge_inv I1 I2) ((map (ii1 chs pns1 pns2 I2 specs2) (comm_specg2_notin_chs specs1 chs))@  
                                          (map (ii2 chs pns1 pns2 I1 specs1) (comm_specg2_notin_chs specs2 chs))) s0"
  unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (elim interrupt_solInf_cg.cases) apply auto
      text \<open>case 1 - 1\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'   
        apply(cases "ch2\<in>chs") 
        subgoal
          apply(cases "ch1\<in>chs") 
          text \<open>In ch1 \<in> chs, In ch2 \<in> chs\<close>
          subgoal
            apply(elim combine_blocks_pairE)
            by auto
          text \<open>In ch1 \<notin> chs, In ch2 \<in> chs\<close>
          subgoal
            apply(elim combine_blocks_unpairE1)
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_solInf_cg.intros(1)[of k])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ tr2])
                      apply auto
                apply(rule interrupt_solInf_cg.intros(1)[of j])
                subgoal by auto
                 apply simp by auto
              done
            done
          done
        subgoal 
          apply(cases "ch1\<in>chs")
          text \<open>In ch1 \<in> chs, In ch2 \<notin> chs\<close>
          subgoal
            apply(elim combine_blocks_unpairE1')
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_solInf_cg.intros(1)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1 _ tr2'])
                      apply auto
                apply(rule interrupt_solInf_cg.intros(1)[of i])
                subgoal by auto
                 apply simp by auto
              done
            done
          text \<open>In ch1 \<notin> chs, In ch2 \<notin> chs\<close>
          subgoal
            apply(elim combine_blocks_unpairE2)
               apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_solInf_cg.intros(1)[of k])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ tr2])
                      apply auto
                apply(rule interrupt_solInf_cg.intros(1)[of j])
                subgoal by auto
                 apply simp by auto
              done
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_solInf_cg.intros(1)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1 _ tr2'])
                      apply auto
                apply(rule interrupt_solInf_cg.intros(1)[of i])
                subgoal by auto
                 apply simp by auto
              done
            done
          done
        done
      text \<open>case 1 - 2\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a b p
        apply(cases "ch1\<in>chs")
        subgoal
          apply(elim combine_blocks_pairE2)
          by auto
        subgoal
          apply(elim combine_blocks_unpairE3)
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_solInf_cg.intros(1)[of k])
              subgoal by auto
               apply simp
               apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ tr2])
                    apply auto
              apply(rule interrupt_solInf_cg.intros(2)[of j])
              subgoal by auto
               apply simp by auto
            done
          done
        done
      text \<open>case 1 - 3\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
        subgoal
          apply(cases "ch1\<in>chs")
          subgoal
            apply(elim combine_blocks_pairE)
            apply auto
            using rdy_of_comm_specg2_prop1[of i specs1 ch1 P]
            using rdy_of_comm_specg2_prop2[of j specs2 ch2 Q]
            using assms
            apply auto
            by (smt (verit, ccfv_SIG) compat_rdy.elims(2) disjoint_iff fst_conv snd_conv)
          subgoal
            apply(elim combine_blocks_unpairE1)
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_solInf_cg.intros(1)[of k])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ tr2])
                    apply auto
                apply(rule interrupt_solInf_cg.intros(3)[of j])
                subgoal by auto
                apply simp by auto
              done
            done
          done
        subgoal
          apply(cases "ch1\<in>chs")
          subgoal
            apply(elim combine_blocks_unpairE1')
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_solInf_cg.intros(3)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1 _ tr2'])
                    apply auto
                apply(rule interrupt_solInf_cg.intros(1)[of i])
                subgoal by auto
                apply simp by auto
              done
            done
          subgoal
            apply(elim combine_blocks_unpairE2)
               apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_solInf_cg.intros(1)[of k])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ tr2])
                      apply auto
                apply(rule interrupt_solInf_cg.intros(3)[of j])
                subgoal by auto
                 apply simp by auto
              done
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_solInf_cg.intros(3)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1 _ tr2'])
                      apply auto
                apply(rule interrupt_solInf_cg.intros(1)[of i])
                subgoal by auto
                 apply simp by auto
              done
            done
          done
        done
      text \<open>case 1 - 4\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a b p
        apply(cases "ch1\<in>chs")
        subgoal
          apply(elim combine_blocks_pairE2)
          by auto
        subgoal
          apply(elim combine_blocks_unpairE3)
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_solInf_cg.intros(1)[of k])
              subgoal by auto
               apply simp
               apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ tr2])
                    apply auto
              apply(rule interrupt_solInf_cg.intros(4)[of j])
              subgoal by auto
               apply simp by auto
            done
          done
        done
      text \<open>case 2 - 1\<close>
      subgoal for i ch1 P d v1 tr1' a b p j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
        subgoal
          apply(elim combine_blocks_pairE2')
          by auto
        subgoal
          apply(elim combine_blocks_unpairE3')
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_solInf_cg.intros(1)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
               apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1 _ tr2'])
                    apply auto
              apply(rule interrupt_solInf_cg.intros(2)[of i])
              subgoal by auto
               apply simp by auto
            done
          done
        done
      text \<open>case 2 - 2\<close>
      subgoal for i ch1 P d1 v1 tr1' a1 b1 p1 j ch2 Q d2 v2 tr2' a2 b2 p2
        apply(cases "d1<d2")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply(auto simp add:assms)
          apply(cases "ch1\<in>chs")
          subgoal
            apply(elim combine_blocks_pairE2) by auto
          subgoal 
            apply(elim combine_blocks_unpairE3)
             apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_solInf_cg.intros(2)[of k])
                subgoal by auto
                    apply simp
                subgoal by auto
                subgoal
                  apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ "(WaitBlkP (d2 - d1) (\<lambda>t. p2 (t + d1)) (rdy_of_comm_specg2 specs2) # InBlockP ch2 v2 # tr2')"])
                        apply auto
                  apply(rule interrupt_solInf_cg.intros(2)[of j])
                  subgoal by auto
                      apply simp
                     apply auto
                  apply(rule delay_inv.intros)
                  by auto
                subgoal
                  by(rule merge_rdy_of_comm_specg2_prop')
                subgoal
                  apply auto
                  apply(rule )
                  by auto
                done
              done
            done
          done
        apply(cases "d1>d2")
        subgoal
          apply(elim combine_blocks_waitE4)
             apply(auto simp add:assms)
          apply(cases "ch2\<in>chs")
          subgoal
            apply(elim combine_blocks_pairE2') by auto
          subgoal 
            apply(elim combine_blocks_unpairE3')
             apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_solInf_cg.intros(2)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                    apply simp
                subgoal by auto
                subgoal
                  apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ "(WaitBlkP (d1 - d2) (\<lambda>t. p1 (t + d2)) (rdy_of_comm_specg2 specs1) # InBlockP ch1 v1 # tr1')" _ "tr2'"])
                        apply auto
                  apply(rule interrupt_solInf_cg.intros(2)[of i])
                  subgoal by auto
                      apply simp
                     apply auto
                  apply(rule delay_inv.intros)
                  by auto
                subgoal
                  by(rule merge_rdy_of_comm_specg2_prop')
                subgoal
                  apply auto
                  apply(rule )
                  by auto
                done
              done
            done
          done
        apply(cases "d1=d2")
        subgoal
          apply(elim combine_blocks_waitE2')
           apply(auto simp add:assms)
          apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE)
              by auto
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_solInf_cg.intros(2)[of k])
                  subgoal by auto
                    apply simp
                  subgoal by auto
                  subgoal
                    apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ "(InBlockP ch2 v2 # tr2')"])
                        apply auto
                    apply(rule interrupt_solInf_cg.intros(1)[of j])
                    subgoal by auto
                      apply simp
                      by auto                  
                  subgoal
                    by(rule merge_rdy_of_comm_specg2_prop')
                  subgoal
                    apply auto
                    apply(rule )
                    by auto
                  done
                done
              done
            done
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_unpairE1')
              apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_solInf_cg.intros(2)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal by auto
                    apply simp
                  subgoal by auto
                  subgoal
                    apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ "(InBlockP ch1 v1 # tr1')" _ "tr2'"])
                        apply auto
                    apply(rule interrupt_solInf_cg.intros(1)[of i])
                    subgoal by auto
                      apply simp
                      by auto
                  subgoal
                    by(rule merge_rdy_of_comm_specg2_prop')
                  subgoal
                    apply auto
                    apply(rule )
                    by auto
                  done
                done
              done
            subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_solInf_cg.intros(2)[of k])
                  subgoal by auto
                    apply simp
                  subgoal by auto
                  subgoal
                    apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ "(InBlockP ch2 v2 # tr2')"])
                        apply auto
                    apply(rule interrupt_solInf_cg.intros(1)[of j])
                    subgoal by auto
                      apply simp
                      by auto                  
                  subgoal
                    by(rule merge_rdy_of_comm_specg2_prop')
                  subgoal
                    apply auto
                    apply(rule )
                    by auto
                  done
                done
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_solInf_cg.intros(2)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal by auto
                    apply simp
                  subgoal by auto
                  subgoal
                    apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ "(InBlockP ch1 v1 # tr1')" _ "tr2'"])
                        apply auto
                    apply(rule interrupt_solInf_cg.intros(1)[of i])
                    subgoal by auto
                      apply simp
                      by auto
                  subgoal
                    by(rule merge_rdy_of_comm_specg2_prop')
                  subgoal
                    apply auto
                    apply(rule )
                    by auto
                  done
                done
              done
            done
          done
        by auto
      text \<open>case 2 - 3\<close>
      subgoal for i ch1 P d v1 tr1' a b p j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
        subgoal
          apply(elim combine_blocks_pairE2')
          by auto
        subgoal
          apply(elim combine_blocks_unpairE3')
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_solInf_cg.intros(3)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
               apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1 _ tr2'])
                    apply auto
              apply(rule interrupt_solInf_cg.intros(2)[of i])
              subgoal by auto
               apply simp by auto
            done
          done
        done
      text \<open>case 2 - 4\<close>
      subgoal for i ch1 P d1 v1 tr1' a1 b1 p1 j ch2 Q d2 v2 tr2' a2 b2 p2
        apply(cases "d1<d2")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply(auto simp add:assms)
          apply(cases "ch1\<in>chs")
          subgoal
            apply(elim combine_blocks_pairE2) by auto
          subgoal 
            apply(elim combine_blocks_unpairE3)
             apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_solInf_cg.intros(2)[of k])
                subgoal by auto
                    apply simp
                subgoal by auto
                subgoal
                  apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ "(WaitBlkP (d2 - d1) (\<lambda>t. p2 (t + d1)) (rdy_of_comm_specg2 specs2) # OutBlockP ch2 v2 # tr2')"])
                        apply auto
                  apply(rule interrupt_solInf_cg.intros(4)[of j])
                  subgoal by auto
                      apply simp
                     apply auto
                  apply(rule delay_inv.intros)
                  by auto
                subgoal
                  by(rule merge_rdy_of_comm_specg2_prop')
                subgoal
                  apply auto
                  apply(rule )
                  by auto
                done
              done
            done
          done
        apply(cases "d1>d2")
        subgoal
          apply(elim combine_blocks_waitE4)
             apply(auto simp add:assms)
          apply(cases "ch2\<in>chs")
          subgoal
            apply(elim combine_blocks_pairE2') by auto
          subgoal 
            apply(elim combine_blocks_unpairE3')
             apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_solInf_cg.intros(4)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                    apply simp
                subgoal by auto
                subgoal
                  apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ "(WaitBlkP (d1 - d2) (\<lambda>t. p1 (t + d2)) (rdy_of_comm_specg2 specs1) # InBlockP ch1 v1 # tr1')" _ "tr2'"])
                        apply auto
                  apply(rule interrupt_solInf_cg.intros(2)[of i])
                  subgoal by auto
                      apply simp
                     apply auto
                  apply(rule delay_inv.intros)
                  by auto
                subgoal
                  by(rule merge_rdy_of_comm_specg2_prop')
                subgoal
                  apply auto
                  apply(rule )
                  by auto
                done
              done
            done
          done
        apply(cases "d1=d2")
        subgoal
          apply(elim combine_blocks_waitE2')
           apply(auto simp add:assms)
          apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE)
                apply auto
              using rdy_of_comm_specg2_prop1[of i specs1 ch1 P]
              using rdy_of_comm_specg2_prop2[of j specs2 ch2 Q]
              using assms
              apply auto
              by (metis Set.set_insert compat_rdy.simps disjoint_insert(2) fst_conv snd_conv)
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_solInf_cg.intros(2)[of k])
                  subgoal by auto
                    apply simp
                  subgoal by auto
                  subgoal
                    apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ "(OutBlockP ch2 v2 # tr2')"])
                        apply auto
                    apply(rule interrupt_solInf_cg.intros(3)[of j])
                    subgoal by auto
                      apply simp
                      by auto                  
                  subgoal
                    by(rule merge_rdy_of_comm_specg2_prop')
                  subgoal
                    apply auto
                    apply(rule )
                    by auto
                  done
                done
              done
            done
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_unpairE1')
              apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_solInf_cg.intros(4)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal by auto
                    apply simp
                  subgoal by auto
                  subgoal
                    apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ "(InBlockP ch1 v1 # tr1')" _ "tr2'"])
                        apply auto
                    apply(rule interrupt_solInf_cg.intros(1)[of i])
                    subgoal by auto
                      apply simp
                      by auto
                  subgoal
                    by(rule merge_rdy_of_comm_specg2_prop')
                  subgoal
                    apply auto
                    apply(rule )
                    by auto
                  done
                done
              done
            subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_solInf_cg.intros(2)[of k])
                  subgoal by auto
                    apply simp
                  subgoal by auto
                  subgoal
                    apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ "(OutBlockP ch2 v2 # tr2')"])
                        apply auto
                    apply(rule interrupt_solInf_cg.intros(3)[of j])
                    subgoal by auto
                      apply simp
                      by auto                  
                  subgoal
                    by(rule merge_rdy_of_comm_specg2_prop')
                  subgoal
                    apply auto
                    apply(rule )
                    by auto
                  done
                done
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_solInf_cg.intros(4)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal by auto
                    apply simp
                  subgoal by auto
                  subgoal
                    apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ "(InBlockP ch1 v1 # tr1')" _ "tr2'"])
                        apply auto
                    apply(rule interrupt_solInf_cg.intros(1)[of i])
                    subgoal by auto
                      apply simp
                      by auto
                  subgoal
                    by(rule merge_rdy_of_comm_specg2_prop')
                  subgoal
                    apply auto
                    apply(rule )
                    by auto
                  done
                done
              done
            done
          done
        by auto
      text \<open>case 3 - 1\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'   
        apply(cases "ch2\<in>chs") 
        subgoal
          apply(cases "ch1\<in>chs") 
          text \<open>In ch1 \<in> chs, In ch2 \<in> chs\<close>
          subgoal
            apply(elim combine_blocks_pairE)
              apply auto
            using rdy_of_comm_specg2_prop2[of i specs1 ch1 P]
            using rdy_of_comm_specg2_prop1[of j specs2 ch2 Q]
            using assms
            apply auto
            by (metis compat_rdy.simps disjoint_insert(2) mk_disjoint_insert prod.collapse)
          text \<open>In ch1 \<notin> chs, In ch2 \<in> chs\<close>
          subgoal
            apply(elim combine_blocks_unpairE1)
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_solInf_cg.intros(3)[of k])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ tr2])
                      apply auto
                apply(rule interrupt_solInf_cg.intros(1)[of j])
                subgoal by auto
                 apply simp by auto
              done
            done
          done
        subgoal 
          apply(cases "ch1\<in>chs")
          text \<open>In ch1 \<in> chs, In ch2 \<notin> chs\<close>
          subgoal
            apply(elim combine_blocks_unpairE1')
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_solInf_cg.intros(1)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1 _ tr2'])
                      apply auto
                apply(rule interrupt_solInf_cg.intros(3)[of i])
                subgoal by auto
                 apply simp by auto
              done
            done
          text \<open>In ch1 \<notin> chs, In ch2 \<notin> chs\<close>
          subgoal
            apply(elim combine_blocks_unpairE2)
               apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_solInf_cg.intros(3)[of k])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ tr2])
                      apply auto
                apply(rule interrupt_solInf_cg.intros(1)[of j])
                subgoal by auto
                 apply simp by auto
              done
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_solInf_cg.intros(1)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1 _ tr2'])
                      apply auto
                apply(rule interrupt_solInf_cg.intros(3)[of i])
                subgoal by auto
                 apply simp by auto
              done
            done
          done
        done
      text \<open>case 3 - 2\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a b p
        apply(cases "ch1\<in>chs")
        subgoal
          apply(elim combine_blocks_pairE2)
          by auto
        subgoal
          apply(elim combine_blocks_unpairE3)
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_solInf_cg.intros(3)[of k])
              subgoal by auto
               apply simp
               apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ tr2])
                    apply auto
              apply(rule interrupt_solInf_cg.intros(2)[of j])
              subgoal by auto
               apply simp by auto
            done
          done
        done
      text \<open>case 3 - 3\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
        subgoal
          apply(cases "ch1\<in>chs")
          subgoal
            apply(elim combine_blocks_pairE)
            by auto
          subgoal
            apply(elim combine_blocks_unpairE1)
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_solInf_cg.intros(3)[of k])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ tr2])
                    apply auto
                apply(rule interrupt_solInf_cg.intros(3)[of j])
                subgoal by auto
                apply simp by auto
              done
            done
          done
        subgoal
          apply(cases "ch1\<in>chs")
          subgoal
            apply(elim combine_blocks_unpairE1')
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_solInf_cg.intros(3)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1 _ tr2'])
                    apply auto
                apply(rule interrupt_solInf_cg.intros(3)[of i])
                subgoal by auto
                apply simp by auto
              done
            done
          subgoal
            apply(elim combine_blocks_unpairE2)
               apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_solInf_cg.intros(3)[of k])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ tr2])
                      apply auto
                apply(rule interrupt_solInf_cg.intros(3)[of j])
                subgoal by auto
                 apply simp by auto
              done
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_solInf_cg.intros(3)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1 _ tr2'])
                      apply auto
                apply(rule interrupt_solInf_cg.intros(3)[of i])
                subgoal by auto
                 apply simp by auto
              done
            done
          done
        done
      text \<open>case 3 - 4\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a b p
        apply(cases "ch1\<in>chs")
        subgoal
          apply(elim combine_blocks_pairE2)
          by auto
        subgoal
          apply(elim combine_blocks_unpairE3)
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_solInf_cg.intros(3)[of k])
              subgoal by auto
               apply simp
               apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ tr2])
                    apply auto
              apply(rule interrupt_solInf_cg.intros(4)[of j])
              subgoal by auto
               apply simp by auto
            done
          done
        done
      text \<open>case 4 - 1\<close>
      subgoal for i ch1 P d v1 tr1' a b p j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
        subgoal
          apply(elim combine_blocks_pairE2')
          by auto
        subgoal
          apply(elim combine_blocks_unpairE3')
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_solInf_cg.intros(1)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
               apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1 _ tr2'])
                    apply auto
              apply(rule interrupt_solInf_cg.intros(4)[of i])
              subgoal by auto
               apply simp by auto
            done
          done
        done
      text \<open>case 4 - 2\<close>
      subgoal for i ch1 P d1 v1 tr1' a1 b1 p1 j ch2 Q d2 v2 tr2' a2 b2 p2
        apply(cases "d1<d2")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply(auto simp add:assms)
          apply(cases "ch1\<in>chs")
          subgoal
            apply(elim combine_blocks_pairE2) by auto
          subgoal 
            apply(elim combine_blocks_unpairE3)
             apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_solInf_cg.intros(4)[of k])
                subgoal by auto
                    apply simp
                subgoal by auto
                subgoal
                  apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ "(WaitBlkP (d2 - d1) (\<lambda>t. p2 (t + d1)) (rdy_of_comm_specg2 specs2) # InBlockP ch2 v2 # tr2')"])
                        apply auto
                  apply(rule interrupt_solInf_cg.intros(2)[of j])
                  subgoal by auto
                      apply simp
                     apply auto
                  apply(rule delay_inv.intros)
                  by auto
                subgoal
                  by(rule merge_rdy_of_comm_specg2_prop')
                subgoal
                  apply auto
                  apply(rule )
                  by auto
                done
              done
            done
          done
        apply(cases "d1>d2")
        subgoal
          apply(elim combine_blocks_waitE4)
             apply(auto simp add:assms)
          apply(cases "ch2\<in>chs")
          subgoal
            apply(elim combine_blocks_pairE2') by auto
          subgoal 
            apply(elim combine_blocks_unpairE3')
             apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_solInf_cg.intros(2)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                    apply simp
                subgoal by auto
                subgoal
                  apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ "(WaitBlkP (d1 - d2) (\<lambda>t. p1 (t + d2)) (rdy_of_comm_specg2 specs1) # OutBlockP ch1 v1 # tr1')" _ "tr2'"])
                        apply auto
                  apply(rule interrupt_solInf_cg.intros(4)[of i])
                  subgoal by auto
                      apply simp
                     apply auto
                  apply(rule delay_inv.intros)
                  by auto
                subgoal
                  by(rule merge_rdy_of_comm_specg2_prop')
                subgoal
                  apply auto
                  apply(rule )
                  by auto
                done
              done
            done
          done
        apply(cases "d1=d2")
        subgoal
          apply(elim combine_blocks_waitE2')
           apply(auto simp add:assms)
          apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE)
              apply auto
              using rdy_of_comm_specg2_prop2[of i specs1 ch1 P]
              using rdy_of_comm_specg2_prop1[of j specs2 ch2 Q]
              using assms
              apply auto
              by (metis Set.set_insert compat_rdy.simps disjoint_insert(2) fst_conv snd_conv)
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_solInf_cg.intros(4)[of k])
                  subgoal by auto
                    apply simp
                  subgoal by auto
                  subgoal
                    apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ "(InBlockP ch2 v2 # tr2')"])
                        apply auto
                    apply(rule interrupt_solInf_cg.intros(1)[of j])
                    subgoal by auto
                      apply simp
                      by auto                  
                  subgoal
                    by(rule merge_rdy_of_comm_specg2_prop')
                  subgoal
                    apply auto
                    apply(rule )
                    by auto
                  done
                done
              done
            done
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_unpairE1')
              apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_solInf_cg.intros(2)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal by auto
                    apply simp
                  subgoal by auto
                  subgoal
                    apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ "(OutBlockP ch1 v1 # tr1')" _ "tr2'"])
                        apply auto
                    apply(rule interrupt_solInf_cg.intros(3)[of i])
                    subgoal by auto
                      apply simp
                      by auto
                  subgoal
                    by(rule merge_rdy_of_comm_specg2_prop')
                  subgoal
                    apply auto
                    apply(rule )
                    by auto
                  done
                done
              done
            subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_solInf_cg.intros(4)[of k])
                  subgoal by auto
                    apply simp
                  subgoal by auto
                  subgoal
                    apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ "(InBlockP ch2 v2 # tr2')"])
                        apply auto
                    apply(rule interrupt_solInf_cg.intros(1)[of j])
                    subgoal by auto
                      apply simp
                      by auto                  
                  subgoal
                    by(rule merge_rdy_of_comm_specg2_prop')
                  subgoal
                    apply auto
                    apply(rule )
                    by auto
                  done
                done
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_solInf_cg.intros(2)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal by auto
                    apply simp
                  subgoal by auto
                  subgoal
                    apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ "(OutBlockP ch1 v1 # tr1')" _ "tr2'"])
                        apply auto
                    apply(rule interrupt_solInf_cg.intros(3)[of i])
                    subgoal by auto
                      apply simp
                      by auto
                  subgoal
                    by(rule merge_rdy_of_comm_specg2_prop')
                  subgoal
                    apply auto
                    apply(rule )
                    by auto
                  done
                done
              done
            done
          done
        by auto
      text \<open>case 4 - 3\<close>
      subgoal for i ch1 P d v1 tr1' a b p j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
        subgoal
          apply(elim combine_blocks_pairE2')
          by auto
        subgoal
          apply(elim combine_blocks_unpairE3')
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_solInf_cg.intros(3)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
               apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1 _ tr2'])
                    apply auto
              apply(rule interrupt_solInf_cg.intros(4)[of i])
              subgoal by auto
               apply simp by auto
            done
          done
        done
      text \<open>case 4 - 4\<close>
      subgoal for i ch1 P d1 v1 tr1' a1 b1 p1 j ch2 Q d2 v2 tr2' a2 b2 p2
        apply(cases "d1<d2")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply(auto simp add:assms)
          apply(cases "ch1\<in>chs")
          subgoal
            apply(elim combine_blocks_pairE2) by auto
          subgoal 
            apply(elim combine_blocks_unpairE3)
             apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_solInf_cg.intros(4)[of k])
                subgoal by auto
                    apply simp
                subgoal by auto
                subgoal
                  apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ "(WaitBlkP (d2 - d1) (\<lambda>t. p2 (t + d1)) (rdy_of_comm_specg2 specs2) # OutBlockP ch2 v2 # tr2')"])
                        apply auto
                  apply(rule interrupt_solInf_cg.intros(4)[of j])
                  subgoal by auto
                      apply simp
                     apply auto
                  apply(rule delay_inv.intros)
                  by auto
                subgoal
                  by(rule merge_rdy_of_comm_specg2_prop')
                subgoal
                  apply auto
                  apply(rule )
                  by auto
                done
              done
            done
          done
        apply(cases "d1>d2")
        subgoal
          apply(elim combine_blocks_waitE4)
             apply(auto simp add:assms)
          apply(cases "ch2\<in>chs")
          subgoal
            apply(elim combine_blocks_pairE2') by auto
          subgoal 
            apply(elim combine_blocks_unpairE3')
             apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_solInf_cg.intros(4)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                    apply simp
                subgoal by auto
                subgoal
                  apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ "(WaitBlkP (d1 - d2) (\<lambda>t. p1 (t + d2)) (rdy_of_comm_specg2 specs1) # OutBlockP ch1 v1 # tr1')" _ "tr2'"])
                        apply auto
                  apply(rule interrupt_solInf_cg.intros(4)[of i])
                  subgoal by auto
                      apply simp
                     apply auto
                  apply(rule delay_inv.intros)
                  by auto
                subgoal
                  by(rule merge_rdy_of_comm_specg2_prop')
                subgoal
                  apply auto
                  apply(rule )
                  by auto
                done
              done
            done
          done
        apply(cases "d1=d2")
        subgoal
          apply(elim combine_blocks_waitE2')
           apply(auto simp add:assms)
          apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE)
                by auto              
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_solInf_cg.intros(4)[of k])
                  subgoal by auto
                    apply simp
                  subgoal by auto
                  subgoal
                    apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ "(OutBlockP ch2 v2 # tr2')"])
                        apply auto
                    apply(rule interrupt_solInf_cg.intros(3)[of j])
                    subgoal by auto
                      apply simp
                      by auto                  
                  subgoal
                    by(rule merge_rdy_of_comm_specg2_prop')
                  subgoal
                    apply auto
                    apply(rule )
                    by auto
                  done
                done
              done
            done
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_unpairE1')
              apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_solInf_cg.intros(4)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal by auto
                    apply simp
                  subgoal by auto
                  subgoal
                    apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ "(OutBlockP ch1 v1 # tr1')" _ "tr2'"])
                        apply auto
                    apply(rule interrupt_solInf_cg.intros(3)[of i])
                    subgoal by auto
                      apply simp
                      by auto
                  subgoal
                    by(rule merge_rdy_of_comm_specg2_prop')
                  subgoal
                    apply auto
                    apply(rule )
                    by auto
                  done
                done
              done
            subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_solInf_cg.intros(4)[of k])
                  subgoal by auto
                    apply simp
                  subgoal by auto
                  subgoal
                    apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ "(OutBlockP ch2 v2 # tr2')"])
                        apply auto
                    apply(rule interrupt_solInf_cg.intros(3)[of j])
                    subgoal by auto
                      apply simp
                      by auto                  
                  subgoal
                    by(rule merge_rdy_of_comm_specg2_prop')
                  subgoal
                    apply auto
                    apply(rule )
                    by auto
                  done
                done
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_solInf_cg.intros(4)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal by auto
                    apply simp
                  subgoal by auto
                  subgoal
                    apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ "(OutBlockP ch1 v1 # tr1')" _ "tr2'"])
                        apply auto
                    apply(rule interrupt_solInf_cg.intros(3)[of i])
                    subgoal by auto
                      apply simp
                      by auto
                  subgoal
                    by(rule merge_rdy_of_comm_specg2_prop')
                  subgoal
                    apply auto
                    apply(rule )
                    by auto
                  done
                done
              done
            done
          done
        by auto
      done
    done
  done

fun com_of_specs1 ::"cname set \<Rightarrow> 'a comm_specg2 \<Rightarrow> 'a comm_specg2 list \<Rightarrow> ((real \<Rightarrow> real \<Rightarrow> 'a gassn2) \<times> (real \<Rightarrow> real \<Rightarrow> 'a gassn2)) list" where
  "com_of_specs1 chs (InSpecg2 ch P) [] = []"
| "com_of_specs1 chs (InSpecg2 ch1 P1) ((InSpecg2 ch2 P2) # l) = com_of_specs1 chs (InSpecg2 ch1 P1) l"
| "com_of_specs1 chs (InSpecg2 ch1 P1) ((OutSpecg2 ch2 P2) # l) = 
          (if ch1 = ch2 \<and> ch1 \<in> chs then (P1,P2) # com_of_specs1 chs (InSpecg2 ch1 P1) l 
                        else com_of_specs1 chs (InSpecg2 ch1 P1) l)"
| "com_of_specs1 chs (OutSpecg2 ch P) [] = []"
| "com_of_specs1 chs (OutSpecg2 ch1 P1) ((OutSpecg2 ch2 P2) # l) = com_of_specs1 chs (OutSpecg2 ch1 P1) l"
| "com_of_specs1 chs (OutSpecg2 ch1 P1) ((InSpecg2 ch2 P2) # l) = 
          (if ch1 = ch2 \<and> ch1 \<in> chs then (P1,P2) # com_of_specs1 chs (OutSpecg2 ch1 P1) l 
                        else com_of_specs1 chs (OutSpecg2 ch1 P1) l)"

fun com_of_specs2 ::"cname set \<Rightarrow> 'a comm_specg2 list \<Rightarrow> 'a comm_specg2 list \<Rightarrow> ((real \<Rightarrow> real \<Rightarrow> 'a gassn2) \<times> (real \<Rightarrow> real \<Rightarrow> 'a gassn2)) list" where
  "com_of_specs2 chs [] l2 = []"
| "com_of_specs2 chs ((InSpecg2 ch P)#l1) l2 = (com_of_specs1 chs (InSpecg2 ch P) l2) @ (com_of_specs2 chs l1 l2)"
| "com_of_specs2 chs ((OutSpecg2 ch P)#l1) l2 = (com_of_specs1 chs (OutSpecg2 ch P) l2) @ (com_of_specs2 chs l1 l2)"

lemma list_prop[simp]:"l1!k = x \<Longrightarrow> k<length l1 \<Longrightarrow> (l1 @ l2)!k = x"
  by (simp add: nth_append)


lemma com_of_specg1_prop1:
 assumes "j < length specs"
     and "specs ! j = OutSpecg2 ch Q"
     and "ch \<in> chs"
   shows "\<exists> k. (com_of_specs1 chs (InSpecg2 ch P) specs)!k = (P,Q) \<and> k < length (com_of_specs1 chs (InSpecg2 ch P) specs)"
using assms 
proof(induction "length specs" arbitrary: j specs)
  case 0
  then show ?case 
    by auto
next
  case (Suc x)
  then show ?case 
    apply(cases specs)
     apply auto
    subgoal for s specs'
      apply(cases s)
      subgoal for ch2 P2
        apply auto
        apply(subgoal_tac "specs'!(j-1) = OutSpecg2 ch Q")
        subgoal
          using Suc(1)[of specs' "j-1"]
          by fastforce
        by (simp add: nth_non_equal_first_eq)
      subgoal for ch2 P2
        apply auto
        subgoal
          apply(cases "j=0")
           apply auto
          subgoal
            apply(rule exI[where x=0]) by auto
          subgoal premises pre
          proof-
            obtain k where kk:"com_of_specs1 chs (InSpecg2 ch2 P) specs' ! k = (P, Q) \<and> k < length(com_of_specs1 chs (InSpecg2 ch2 P) specs')"
              using pre(1)[of specs' "j-1"] using pre by fastforce
            show ?thesis
              apply(rule exI[where x="k+1"])
              using kk by auto
          qed
          done
        apply(subgoal_tac "specs'!(j-1) = OutSpecg2 ch Q")
        subgoal
          using Suc(1)[of specs' "j-1"]
          by fastforce
        by (simp add: nth_non_equal_first_eq)
      done
    done
qed

lemma com_of_specg1_prop2:
 assumes "j < length specs"
     and "specs ! j = InSpecg2 ch Q"
     and "ch \<in> chs"
   shows "\<exists> k. (com_of_specs1 chs (OutSpecg2 ch P) specs)!k = (P,Q) \<and> k < length (com_of_specs1 chs (OutSpecg2 ch P) specs)"
using assms 
proof(induction "length specs" arbitrary: j specs)
  case 0
  then show ?case 
    by auto
next
  case (Suc x)
  then show ?case 
    apply(cases specs)
     apply auto
    subgoal for s specs'
      apply(cases s)
      subgoal for ch2 P2
        apply auto
        subgoal
          apply(cases "j=0")
           apply auto
          subgoal
            apply(rule exI[where x=0]) by auto
          subgoal premises pre
          proof-
            obtain k where kk:"com_of_specs1 chs (OutSpecg2 ch2 P) specs' ! k = (P, Q) \<and> k < length(com_of_specs1 chs (OutSpecg2 ch2 P) specs')"
              using pre(1)[of specs' "j-1"] using pre by fastforce
            show ?thesis
              apply(rule exI[where x="k+1"])
              using kk by auto
          qed
          done
        apply(subgoal_tac "specs'!(j-1) = InSpecg2 ch Q")
        subgoal
          using Suc(1)[of specs' "j-1"]
          by fastforce
        by (simp add: nth_non_equal_first_eq)
      subgoal for ch2 P2
        apply auto
        apply(subgoal_tac "specs'!(j-1) = InSpecg2 ch Q")
        subgoal
          using Suc(1)[of specs' "j-1"]
          by fastforce
        by (simp add: nth_non_equal_first_eq)
      done
    done
qed


lemma com_of_specg2_prop1:
 assumes "i < length specs1"
     and "specs1 ! i = InSpecg2 ch P"
     and "j < length specs2"
     and "specs2 ! j = OutSpecg2 ch Q"
     and "ch \<in> chs"
   shows "\<exists> k. (com_of_specs2 chs specs1 specs2)!k = (P,Q) \<and> k < length (com_of_specs2 chs specs1 specs2)"
using assms 
proof(induction "length specs1" arbitrary: i specs1)
  case 0
  then show ?case 
    by auto
next
  case (Suc x)
  then show ?case 
    apply(cases specs1)
     apply auto
    subgoal for s1 specs1'
      apply(cases s1)
      subgoal for ch1 P1
        apply auto
        apply(cases "i=0")
        apply auto
        subgoal premises pre
        proof-
          obtain k where kk:"(com_of_specs1 chs (InSpecg2 ch P) specs2) ! k = (P, Q) \<and> k<length(com_of_specs1 chs (InSpecg2 ch P) specs2)"
            using com_of_specg1_prop1[of j specs2 ch Q chs P] pre by auto
          show ?thesis
            apply(rule exI[where x=k])
            using kk by auto
        qed
        subgoal premises pre
        proof-
          obtain k where kk:"com_of_specs2 chs specs1' specs2 ! k = (P, Q) \<and> k < length (com_of_specs2 chs specs1' specs2)"
            using pre(1)[of specs1' "i-1"] pre by fastforce
          show ?thesis
            apply(rule exI[where x="length (com_of_specs1 chs (InSpecg2 ch1 P1) specs2)+k"])
            using kk by auto
        qed
        done
      subgoal for ch1 P1
        apply auto
        apply(cases "i=0")
         apply auto
        subgoal premises pre
        proof-
          obtain k where kk:"com_of_specs2 chs specs1' specs2 ! k = (P,Q) \<and> k < length (com_of_specs2 chs specs1' specs2)"
            using pre(1)[of specs1' "i-1"] pre by fastforce
          show ?thesis
            apply(rule exI[where x="length (com_of_specs1 chs (OutSpecg2 ch1 P1) specs2)+k"])
            using kk by auto
        qed
        done
      done
    done
qed


lemma com_of_specg2_prop2:
 assumes "i < length specs1"
     and "specs1 ! i = OutSpecg2 ch P"
     and "j < length specs2"
     and "specs2 ! j = InSpecg2 ch Q"
     and "ch \<in> chs"
   shows "\<exists> k. (com_of_specs2 chs specs1 specs2)!k = (P,Q) \<and> k < length (com_of_specs2 chs specs1 specs2)"
using assms 
proof(induction "length specs1" arbitrary: i specs1)
  case 0
  then show ?case 
    by auto
next
  case (Suc x)
  then show ?case 
    apply(cases specs1)
     apply auto
    subgoal for s1 specs1'
      apply(cases s1)
      subgoal for ch1 P1
        apply auto
        apply(cases "i=0")
         apply auto
        subgoal premises pre
        proof-
          obtain k where kk:"com_of_specs2 chs specs1' specs2 ! k = (P,Q) \<and> k < length (com_of_specs2 chs specs1' specs2)"
            using pre(1)[of specs1' "i-1"] pre by fastforce
          show ?thesis
            apply(rule exI[where x="length (com_of_specs1 chs (InSpecg2 ch1 P1) specs2)+k"])
            using kk by auto
        qed
        done
      subgoal for ch1 P1
        apply auto
        apply(cases "i=0")
        apply auto
        subgoal premises pre
        proof-
          obtain k where kk:"(com_of_specs1 chs (OutSpecg2 ch P) specs2) ! k = (P,Q) \<and> k<length(com_of_specs1 chs (OutSpecg2 ch P) specs2)"
            using com_of_specg1_prop2[of j specs2 ch Q chs P] pre by auto
          show ?thesis
            apply(rule exI[where x=k])
            using kk by auto
        qed
        subgoal premises pre
        proof-
          obtain k where kk:"com_of_specs2 chs specs1' specs2 ! k = (P,Q) \<and> k < length (com_of_specs2 chs specs1' specs2)"
            using pre(1)[of specs1' "i-1"] pre by fastforce
          show ?thesis
            apply(rule exI[where x="length (com_of_specs1 chs (OutSpecg2 ch1 P1) specs2)+k"])
            using kk by auto
        qed
        done
      done
    done
qed

inductive com_of_specs22_sync::"cname set \<Rightarrow> pname set \<Rightarrow> pname set \<Rightarrow> ((real \<Rightarrow> real \<Rightarrow> 'a gassn2) \<times> (real \<Rightarrow> real \<Rightarrow> 'a gassn2)) list \<Rightarrow> 'a gassn2" where
  " l= (P,Q)#l' \<Longrightarrow>  
    (\<exists>\<^sub>gv. sync_gassn chs pns1 pns2 (P 0 v)(Q 0 v)) s0 s tr \<or> com_of_specs22_sync chs pns1 pns2 l' s0 s tr\<Longrightarrow>
    com_of_specs22_sync chs pns1 pns2 l s0 s tr "

lemma com_of_specs22_sync_prop0:"com_of_specs22_sync chs pns1 pns2 [] = false_gassn"
  unfolding false_gassn_def
  apply rule+
   apply auto
  apply(elim com_of_specs22_sync.cases)
  by auto

lemma com_of_specs22_sync_prop:
 assumes "i < length l"
     and "l!i = (P,Q)"     
   shows "(\<exists>\<^sub>gv. sync_gassn chs pns1 pns2 (P 0 v)(Q 0 v)) s0 s tr \<Longrightarrow> com_of_specs22_sync chs pns1 pns2 l s0 s tr"
  using assms
proof(induction "length l" arbitrary: l i)
  case 0
  then show ?case by auto
next
  case (Suc x)
  then show ?case 
    apply(cases "i=0")
    subgoal
      apply auto
      apply(cases l)
       apply auto
      subgoal for l'
      apply(rule com_of_specs22_sync.intros)
        by auto
      done
    apply auto
    apply(cases l)
       apply auto
    subgoal for a b l'
      apply(rule com_of_specs22_sync.intros[of _ a b l'])
      apply auto
      using Suc(1)[of l' "i-1"]
      by auto
    done
qed

lemma com_of_specs22_sync_prop1:
 assumes "i < length specs1"
     and "specs1 ! i = InSpecg2 ch P"
     and "j < length specs2"
     and "specs2 ! j = OutSpecg2 ch Q"
     and "ch \<in> chs"
     and "(\<exists>\<^sub>gv. sync_gassn chs pns1 pns2 (P 0 v)(Q 0 v)) s0 s tr"
   shows "com_of_specs22_sync chs pns1 pns2 (com_of_specs2 chs specs1 specs2) s0 s tr"
proof-
  obtain k where kk:"(com_of_specs2 chs specs1 specs2)!k = (P,Q) \<and> k < length (com_of_specs2 chs specs1 specs2)"
    using com_of_specg2_prop1[of i specs1 ch P j specs2 Q chs]  assms by blast
  show ?thesis
    apply(rule com_of_specs22_sync_prop[of k _ P Q])
    using kk assms by auto
qed


lemma com_of_specs22_sync_prop2:
 assumes "i < length specs1"
     and "specs1 ! i = OutSpecg2 ch P"
     and "j < length specs2"
     and "specs2 ! j = InSpecg2 ch Q"
     and "ch \<in> chs"
     and "(\<exists>\<^sub>gv. sync_gassn chs pns1 pns2 (P 0 v)(Q 0 v)) s0 s tr"
   shows "com_of_specs22_sync chs pns1 pns2 (com_of_specs2 chs specs1 specs2) s0 s tr"
proof-
  obtain k where kk:"(com_of_specs2 chs specs1 specs2)!k = (P,Q) \<and> k < length (com_of_specs2 chs specs1 specs2)"
    using com_of_specg2_prop2[of i specs1 ch P j specs2 Q chs]  assms by blast
  show ?thesis
    apply(rule com_of_specs22_sync_prop[of k _ P Q])
    using kk assms by auto
qed

lemma sync_gassn_interrupt_solInf_interrupt_solInf2:
  assumes "\<not>compat_rdy (rdy_of_comm_specg2 specs1) (rdy_of_comm_specg2 specs2)"
shows
  "sync_gassn chs pns1 pns2 (interrupt_solInf_cg I1 specs1) (interrupt_solInf_cg I2 specs2) s0 \<Longrightarrow>\<^sub>G
   interrupt_sol_cg (merge_inv I1 I2) pp (\<lambda>_ .0) (\<lambda>_ . com_of_specs22_sync chs pns1 pns2 (com_of_specs2 chs specs1 specs2))((map (ii1 chs pns1 pns2 I2 specs2) (comm_specg2_notin_chs specs1 chs))@  
                                          (map (ii2 chs pns1 pns2 I1 specs1) (comm_specg2_notin_chs specs2 chs))) s0"
unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply (elim interrupt_solInf_cg.cases) apply auto
      text \<open>case 1 - 1\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs") 
        subgoal
          apply(cases "ch1\<in>chs") 
          text \<open>In ch1 \<in> chs, In ch2 \<in> chs\<close>
          subgoal
            apply(elim combine_blocks_pairE)
            by auto
          text \<open>In ch1 \<notin> chs, In ch2 \<in> chs\<close>
          subgoal
            apply(elim combine_blocks_unpairE1)
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of k])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ tr2])
                      apply auto
                apply(rule interrupt_solInf_cg.intros(1)[of j])
                subgoal by auto
                 apply simp by auto
              done
            done
          done
        subgoal 
          apply(cases "ch1\<in>chs")
          text \<open>In ch1 \<in> chs, In ch2 \<notin> chs\<close>
          subgoal
            apply(elim combine_blocks_unpairE1')
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1 _ tr2'])
                      apply auto
                apply(rule interrupt_solInf_cg.intros(1)[of i])
                subgoal by auto
                 apply simp by auto
              done
            done
          text \<open>In ch1 \<notin> chs, In ch2 \<notin> chs\<close>
          subgoal
            apply(elim combine_blocks_unpairE2)
               apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of k])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ tr2])
                      apply auto
                apply(rule interrupt_solInf_cg.intros(1)[of j])
                subgoal by auto
                 apply simp by auto
              done
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1 _ tr2'])
                      apply auto
                apply(rule interrupt_solInf_cg.intros(1)[of i])
                subgoal by auto
                 apply simp by auto
              done
            done
          done
        done
      text \<open>case 1 - 2\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a b p
        apply(cases "ch1\<in>chs")
        subgoal
          apply(elim combine_blocks_pairE2)
          by auto
        subgoal
          apply(elim combine_blocks_unpairE3)
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of k])
              subgoal by auto
               apply simp
               apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ tr2])
                    apply auto
              apply(rule interrupt_solInf_cg.intros(2)[of j])
              subgoal by auto
               apply simp by auto
            done
          done
        done
      text \<open>case 1 - 3\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
        subgoal
          apply(cases "ch1\<in>chs")
          subgoal
            apply(elim combine_blocks_pairE)
            apply auto
            apply(rule interrupt_sol_cg.intros(2))
             apply auto
            apply(rule com_of_specs22_sync_prop1[of i _ ch2 P j _ Q])
                 apply auto
            unfolding exists_gassn_def
            apply(rule exI[where x= v2])
            apply(rule )
            by auto
          subgoal
            apply(elim combine_blocks_unpairE1)
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of k])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ tr2])
                    apply auto
                apply(rule interrupt_solInf_cg.intros(3)[of j])
                subgoal by auto
                apply simp by auto
              done
            done
          done
        subgoal
          apply(cases "ch1\<in>chs")
          subgoal
            apply(elim combine_blocks_unpairE1')
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1 _ tr2'])
                    apply auto
                apply(rule interrupt_solInf_cg.intros(1)[of i])
                subgoal by auto
                apply simp by auto
              done
            done
          subgoal
            apply(elim combine_blocks_unpairE2)
               apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of k])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ tr2])
                      apply auto
                apply(rule interrupt_solInf_cg.intros(3)[of j])
                subgoal by auto
                 apply simp by auto
              done
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1 _ tr2'])
                      apply auto
                apply(rule interrupt_solInf_cg.intros(1)[of i])
                subgoal by auto
                 apply simp by auto
              done
            done
          done
        done
      text \<open>case 1 - 4\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a b p
        apply(cases "ch1\<in>chs")
        subgoal
          apply(elim combine_blocks_pairE2)
          by auto
        subgoal
          apply(elim combine_blocks_unpairE3)
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of k])
              subgoal by auto
               apply simp
               apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ tr2])
                    apply auto
              apply(rule interrupt_solInf_cg.intros(4)[of j])
              subgoal by auto
               apply simp by auto
            done
          done
        done
      text \<open>case 2 - 1\<close>
      subgoal for i ch1 P d v1 tr1' a b p j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
        subgoal
          apply(elim combine_blocks_pairE2')
          by auto
        subgoal
          apply(elim combine_blocks_unpairE3')
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
               apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1 _ tr2'])
                    apply auto
              apply(rule interrupt_solInf_cg.intros(2)[of i])
              subgoal by auto
               apply simp by auto
            done
          done
        done
      text \<open>case 2 - 2\<close>
      subgoal for i ch1 P d1 v1 tr1' a1 b1 p1 j ch2 Q d2 v2 tr2' a2 b2 p2
        apply(elim combine_blocks_waitE1)
        using assms by auto
      text \<open>case 2 - 3\<close>
      subgoal for i ch1 P d v1 tr1' a b p j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
        subgoal
          apply(elim combine_blocks_pairE2')
          by auto
        subgoal
          apply(elim combine_blocks_unpairE3')
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
               apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1 _ tr2'])
                    apply auto
              apply(rule interrupt_solInf_cg.intros(2)[of i])
              subgoal by auto
               apply simp by auto
            done
          done
        done
      text \<open>case 2 - 4\<close>
      subgoal for i ch1 P d1 v1 tr1' a1 b1 p1 j ch2 Q d2 v2 tr2' a2 b2 p2
        apply(elim combine_blocks_waitE1)
        using assms by auto
      text \<open>case 3 - 1\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'   
        apply(cases "ch2\<in>chs") 
        subgoal
          apply(cases "ch1\<in>chs") 
          text \<open>In ch1 \<in> chs, In ch2 \<in> chs\<close>
          subgoal
            apply(elim combine_blocks_pairE)
              apply auto
            apply(rule interrupt_sol_cg.intros(2))
             apply auto
            apply(rule com_of_specs22_sync_prop2[of i _ ch2 P j _ Q])
                 apply auto
            unfolding exists_gassn_def
            apply(rule exI[where x= v2])
            apply(rule )
            by auto
          text \<open>In ch1 \<notin> chs, In ch2 \<in> chs\<close>
          subgoal
            apply(elim combine_blocks_unpairE1)
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of k])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ tr2])
                      apply auto
                apply(rule interrupt_solInf_cg.intros(1)[of j])
                subgoal by auto
                 apply simp by auto
              done
            done
          done
        subgoal 
          apply(cases "ch1\<in>chs")
          text \<open>In ch1 \<in> chs, In ch2 \<notin> chs\<close>
          subgoal
            apply(elim combine_blocks_unpairE1')
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1 _ tr2'])
                      apply auto
                apply(rule interrupt_solInf_cg.intros(3)[of i])
                subgoal by auto
                 apply simp by auto
              done
            done
          text \<open>In ch1 \<notin> chs, In ch2 \<notin> chs\<close>
          subgoal
            apply(elim combine_blocks_unpairE2)
               apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of k])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ tr2])
                      apply auto
                apply(rule interrupt_solInf_cg.intros(1)[of j])
                subgoal by auto
                 apply simp by auto
              done
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1 _ tr2'])
                      apply auto
                apply(rule interrupt_solInf_cg.intros(3)[of i])
                subgoal by auto
                 apply simp by auto
              done
            done
          done
        done
      text \<open>case 3 - 2\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a b p
        apply(cases "ch1\<in>chs")
        subgoal
          apply(elim combine_blocks_pairE2)
          by auto
        subgoal
          apply(elim combine_blocks_unpairE3)
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of k])
              subgoal by auto
               apply simp
               apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ tr2])
                    apply auto
              apply(rule interrupt_solInf_cg.intros(2)[of j])
              subgoal by auto
               apply simp by auto
            done
          done
        done
      text \<open>case 3 - 3\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
        subgoal
          apply(cases "ch1\<in>chs")
          subgoal
            apply(elim combine_blocks_pairE)
            by auto
          subgoal
            apply(elim combine_blocks_unpairE1)
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of k])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ tr2])
                    apply auto
                apply(rule interrupt_solInf_cg.intros(3)[of j])
                subgoal by auto
                apply simp by auto
              done
            done
          done
        subgoal
          apply(cases "ch1\<in>chs")
          subgoal
            apply(elim combine_blocks_unpairE1')
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1 _ tr2'])
                    apply auto
                apply(rule interrupt_solInf_cg.intros(3)[of i])
                subgoal by auto
                apply simp by auto
              done
            done
          subgoal
            apply(elim combine_blocks_unpairE2)
               apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of k])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ tr2])
                      apply auto
                apply(rule interrupt_solInf_cg.intros(3)[of j])
                subgoal by auto
                 apply simp by auto
              done
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1 _ tr2'])
                      apply auto
                apply(rule interrupt_solInf_cg.intros(3)[of i])
                subgoal by auto
                 apply simp by auto
              done
            done
          done
        done
      text \<open>case 3 - 4\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a b p
        apply(cases "ch1\<in>chs")
        subgoal
          apply(elim combine_blocks_pairE2)
          by auto
        subgoal
          apply(elim combine_blocks_unpairE3)
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of k])
              subgoal by auto
               apply simp
               apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1' _ tr2])
                    apply auto
              apply(rule interrupt_solInf_cg.intros(4)[of j])
              subgoal by auto
               apply simp by auto
            done
          done
        done
      text \<open>case 4 - 1\<close>
      subgoal for i ch1 P d v1 tr1' a b p j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
        subgoal
          apply(elim combine_blocks_pairE2')
          by auto
        subgoal
          apply(elim combine_blocks_unpairE3')
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
               apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1 _ tr2'])
                    apply auto
              apply(rule interrupt_solInf_cg.intros(4)[of i])
              subgoal by auto
               apply simp by auto
            done
          done
        done
      text \<open>case 4 - 2\<close>
      subgoal for i ch1 P d1 v1 tr1' a1 b1 p1 j ch2 Q d2 v2 tr2' a2 b2 p2
        apply(elim combine_blocks_waitE1)
        using assms by auto
      text \<open>case 4 - 3\<close>
      subgoal for i ch1 P d v1 tr1' a b p j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
        subgoal
          apply(elim combine_blocks_pairE2')
          by auto
        subgoal
          apply(elim combine_blocks_unpairE3')
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
               apply(rule sync_gassn.intros[of _ _ _ _ _ _ _ tr1 _ tr2'])
                    apply auto
              apply(rule interrupt_solInf_cg.intros(4)[of i])
              subgoal by auto
               apply simp by auto
            done
          done
        done
      text \<open>case 4 - 4\<close>
      subgoal for i ch1 P d1 v1 tr1' a1 b1 p1 j ch2 Q d2 v2 tr2' a2 b2 p2
        apply(elim combine_blocks_waitE1)
        using assms 
        by auto
      done
    done
  done


fun if1:: "cname set \<Rightarrow> pname set \<Rightarrow> pname set \<Rightarrow> 'a gpinv2 \<Rightarrow> pname \<Rightarrow> 'a eexp \<Rightarrow> (real \<Rightarrow> 'a gassn2) \<Rightarrow> 'a comm_specg2 list \<Rightarrow> 'a comm_specg2 \<Rightarrow> 'a comm_specg2" where
  "if1 chs pns1 pns2 I pn e PP specs (InSpecg2 ch P) 
     = (InSpecg2 ch (\<lambda> d v. sync_gassn chs pns1 pns2 (P d v) 
                      (interrupt_sol_cg (delay_inv d I) pn (\<lambda> s. e s - d) (\<lambda> t. PP(t+d)) (map (spec_wait_of d) specs))))"
| "if1 chs pns1 pns2 I pn e PP specs (OutSpecg2 ch P) 
     = (OutSpecg2 ch (\<lambda> d v. sync_gassn chs pns1 pns2 (P d v) 
                      (interrupt_sol_cg (delay_inv d I) pn (\<lambda> s. e s - d) (\<lambda> t. PP(t+d)) (map (spec_wait_of d) specs))))"

fun if2:: "cname set \<Rightarrow> pname set \<Rightarrow> pname set \<Rightarrow> 'a gpinv2 \<Rightarrow> pname \<Rightarrow> 'a eexp \<Rightarrow> (real \<Rightarrow> 'a gassn2) \<Rightarrow> 'a comm_specg2 list \<Rightarrow> 'a comm_specg2 \<Rightarrow> 'a comm_specg2" where
  "if2 chs pns1 pns2 I pn e PP specs (InSpecg2 ch P) 
     = (InSpecg2 ch (\<lambda> d v. sync_gassn chs pns1 pns2  
                      (interrupt_sol_cg (delay_inv d I) pn (\<lambda> s. e s - d) (\<lambda> t. PP(t+d)) (map (spec_wait_of d) specs)) (P d v)))"
| "if2 chs pns1 pns2 I pn e PP specs (OutSpecg2 ch P) 
     = (OutSpecg2 ch (\<lambda> d v. sync_gassn chs pns1 pns2  
                      (interrupt_sol_cg (delay_inv d I) pn (\<lambda> s. e s - d) (\<lambda> t. PP(t+d)) (map (spec_wait_of d) specs)) (P d v)))"




lemma rdy_of_if:"rdy_of_comm_specg2 ((map (if1 chs pns1 pns2 I1 pn1 e1 PP1 specs1) L1)@  
                                          (map (if2 chs pns3 pns4 I2 pn2 e2 PP2 specs2) L2)) = 
                    rdy_of_comm_specg2 (L1 @ L2)"
proof(induction "length L1 + length L2"  arbitrary: L1 L2 rule: less_induct)
  case less
  show ?case 
    apply(cases L1)
    subgoal
      apply(cases L2)
      subgoal by auto
      subgoal for a2 l2
        apply(cases a2)
        subgoal 
          using less[of "[]" l2]
          by(auto simp add: rdy_of_comm_specg2_def)  
        subgoal 
          using less[of "[]" l2]
          by(auto simp add: rdy_of_comm_specg2_def)
        done
      done
    subgoal for a1 l1
      apply auto
      apply(cases a1)
      subgoal
        using less[of l1 L2]
        by(auto simp add: rdy_of_comm_specg2_def)
      subgoal
        using less[of l1 L2]
        by(auto simp add: rdy_of_comm_specg2_def)
      done
    done
qed
                         


lemma merge_rdy_of_comm_specg2_prop'':"merge_rdy chs (rdy_of_comm_specg2 specs1) (rdy_of_comm_specg2 specs2) = 
                      rdy_of_comm_specg2
     (map (if1 chs pns1 pns2 I2 pn2 e2 G2 specs2) (comm_specg2_notin_chs specs1 chs) @
      map (if2 chs pns1 pns2 I1 pn1 e1 G1 specs1) (comm_specg2_notin_chs specs2 chs))"
  apply(subst rdy_of_if[of chs pns1 pns2 I2 pn2 e2 G2 specs2 "(comm_specg2_notin_chs specs1 chs)" pns1 pns2 I1 pn1 e1 G1 specs1 "(comm_specg2_notin_chs specs2 chs)"])
  by(rule merge_rdy_of_comm_specg2_prop)

lemma rdy_of_iif:"rdy_of_comm_specg2 ((map (ii1 chs pns1 pns2 I1 specs1) L1)@  
                                          (map (if2 chs pns3 pns4 I2 pn2 e2 PP2 specs2) L2)) = 
                    rdy_of_comm_specg2 (L1 @ L2)"
proof(induction "length L1 + length L2"  arbitrary: L1 L2 rule: less_induct)
  case less
  show ?case 
    apply(cases L1)
    subgoal
      apply(cases L2)
      subgoal by auto
      subgoal for a2 l2
        apply(cases a2)
        subgoal 
          using less[of "[]" l2]
          by(auto simp add: rdy_of_comm_specg2_def)  
        subgoal 
          using less[of "[]" l2]
          by(auto simp add: rdy_of_comm_specg2_def)
        done
      done
    subgoal for a1 l1
      apply auto
      apply(cases a1)
      subgoal
        using less[of l1 L2]
        by(auto simp add: rdy_of_comm_specg2_def)
      subgoal
        using less[of l1 L2]
        by(auto simp add: rdy_of_comm_specg2_def)
      done
    done
qed

lemma merge_rdy_of_comm_specg2_prop''':"merge_rdy chs (rdy_of_comm_specg2 specs1) (rdy_of_comm_specg2 specs2) = 
                      rdy_of_comm_specg2
     (map (ii1 chs pns1 pns2 I2 specs2) (comm_specg2_notin_chs specs1 chs) @
      map (if2 chs pns1 pns2 I1 pn1 e1 G1 specs1) (comm_specg2_notin_chs specs2 chs))"
  apply(subst rdy_of_iif[of chs pns1 pns2 I2 specs2 "(comm_specg2_notin_chs specs1 chs)" pns1 pns2 I1 pn1 e1 G1 specs1 "(comm_specg2_notin_chs specs2 chs)"])
  by(rule merge_rdy_of_comm_specg2_prop)


lemma rdy_of_ifi:"rdy_of_comm_specg2 ((map (if1 chs pns1 pns2 I1 pn1 e1 PP1 specs1) L1)@  
                                          (map (ii2 chs pns3 pns4 I2 specs2) L2)) = 
                    rdy_of_comm_specg2 (L1 @ L2)"
proof(induction "length L1 + length L2"  arbitrary: L1 L2 rule: less_induct)
  case less
  show ?case 
    apply(cases L1)
    subgoal
      apply(cases L2)
      subgoal by auto
      subgoal for a2 l2
        apply(cases a2)
        subgoal 
          using less[of "[]" l2]
          by(auto simp add: rdy_of_comm_specg2_def)  
        subgoal 
          using less[of "[]" l2]
          by(auto simp add: rdy_of_comm_specg2_def)
        done
      done
    subgoal for a1 l1
      apply auto
      apply(cases a1)
      subgoal
        using less[of l1 L2]
        by(auto simp add: rdy_of_comm_specg2_def)
      subgoal
        using less[of l1 L2]
        by(auto simp add: rdy_of_comm_specg2_def)
      done
    done
qed

lemma merge_rdy_of_comm_specg2_prop'''':"merge_rdy chs (rdy_of_comm_specg2 specs1) (rdy_of_comm_specg2 specs2) = 
                      rdy_of_comm_specg2
     (map (if1 chs pns1 pns2 I2 pn2 e2 G2 specs2) (comm_specg2_notin_chs specs1 chs) @
      map (ii2 chs pns1 pns2 I1 specs1) (comm_specg2_notin_chs specs2 chs))"
  apply(subst rdy_of_ifi[of chs pns1 pns2 I2 pn2 e2 G2 specs2 "(comm_specg2_notin_chs specs1 chs)" pns1 pns2 I1 specs1 "(comm_specg2_notin_chs specs2 chs)"])
  by(rule merge_rdy_of_comm_specg2_prop)

lemma sync_gassn_interrupt_sol_interrupt_sol1:
  assumes "compat_rdy (rdy_of_comm_specg2 specs1) (rdy_of_comm_specg2 specs2)" 
     and  "pn1 \<in> pns1 \<and> pn2 \<in> pns2 \<and> pns1 \<inter> pns2 = {}"
shows
  "sync_gassn chs pns1 pns2 (interrupt_sol_cg I1 pn1 e1 G1 specs1) (interrupt_sol_cg I2 pn2 e2 G2 specs2) s0 \<Longrightarrow>\<^sub>G
   (IFG (\<lambda> s0. e1 (the (s0 pn1)) > e2 (the (s0 pn2)) \<and> e1 (the (s0 pn1)) > 0) 
    THEN
          interrupt_sol_cg (merge_inv I1 I2) pn2 e2 
      (\<lambda> d. sync_gassn chs pns1 pns2 (interrupt_sol_cg (delay_inv d I1) pn1 (\<lambda>s. e1 s - d) (\<lambda> t. G1 (t+d)) (map (spec_wait_of d) specs1)) (G2 d))
         ((map (if1 chs pns1 pns2 I2 pn2 e2 G2 specs2) (comm_specg2_notin_chs specs1 chs))@  
          (map (if2 chs pns1 pns2 I1 pn1 e1 G1 specs1) (comm_specg2_notin_chs specs2 chs))) 
    ELSE
        (IFG (\<lambda> s0. e1 (the (s0 pn1)) < e2 (the (s0 pn2)) \<and> e2 (the (s0 pn2)) > 0)
         THEN interrupt_sol_cg (merge_inv I1 I2) pn1 e1 
      (\<lambda> d. sync_gassn chs pns1 pns2 (G1 d) (interrupt_sol_cg (delay_inv d I2) pn2 (\<lambda>s. e2 s - d) (\<lambda> t. G2 (t+d)) (map (spec_wait_of d) specs2)))
         ((map (if1 chs pns1 pns2 I2 pn2 e2 G2 specs2) (comm_specg2_notin_chs specs1 chs))@  
          (map (if2 chs pns1 pns2 I1 pn1 e1 G1 specs1) (comm_specg2_notin_chs specs2 chs)))
         ELSE interrupt_sol_cg (merge_inv I1 I2) pn1 e1 
      (\<lambda> d. sync_gassn chs pns1 pns2 (G1 d) (interrupt_sol_cg (delay_inv d I2) pn2 (\<lambda>s. e2 s - d) (\<lambda> t. G2 (t+d)) (map (spec_wait_of d) specs2))
         \<or>\<^sub>g sync_gassn chs pns1 pns2 (interrupt_sol_cg (delay_inv d I1) pn1 (\<lambda>s. e1 s - d) (\<lambda> t. G1 (t+d)) (map (spec_wait_of d) specs1)) (G2 d))
         ((map (if1 chs pns1 pns2 I2 pn2 e2 G2 specs2) (comm_specg2_notin_chs specs1 chs))@  
          (map (if2 chs pns1 pns2 I1 pn1 e1 G1 specs1) (comm_specg2_notin_chs specs2 chs)))
         FI) 
    FI) 
  s0"
unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply(subgoal_tac"e1 (the (s0 pn1)) = e1 (the (s11 pn1))")
       prefer 2
      subgoal 
        apply auto
        apply(subst merge_state_eval1[of pn1]) using assms by auto
      apply(subgoal_tac"e2 (the (s0 pn2)) = e2 (the (s12 pn2))")
       prefer 2
      subgoal 
        apply auto
        apply(subst merge_state_eval2[of pn2]) using assms by auto
      apply (elim interrupt_sol_cg.cases) apply auto
      text \<open>case 1 - 1\<close>
      subgoal for tr1' a1 b1 p1 tr2' a2 b2 p2
        apply(cases"e1 (the (s11 pn1)) > e2 (the (s12 pn2))")
        subgoal 
          unfolding cond_gassn2_def
          apply auto
          apply(elim combine_blocks_waitE4)
             apply (auto simp add:assms)
          subgoal for tr'
            apply(rule interrupt_sol_cg.intros(1))
                apply auto
            subgoal
              apply(rule sync_gassn.intros)
                    apply auto[4]
                prefer 3
                apply simp
              apply(rule interrupt_sol_cg.intros(1))
                    apply auto
                apply rule
                by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
              apply(rule merge_rdy_of_comm_specg2_prop'')
              apply(rule merge_inv.intros)
            by auto
          done
        apply(cases"e1 (the (s11 pn1)) < e2 (the (s12 pn2))")
        subgoal
          unfolding cond_gassn2_def
          apply auto
          apply(elim combine_blocks_waitE3)
             apply (auto simp add:assms)
          subgoal for tr'
            apply(rule interrupt_sol_cg.intros(1))
                apply auto
            subgoal
              apply(rule sync_gassn.intros)
                    apply auto[4]
                prefer 3
                apply simp
              apply auto
              apply(rule interrupt_sol_cg.intros)
              apply auto
              apply rule
              by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
              apply(rule merge_rdy_of_comm_specg2_prop'')
            apply(rule merge_inv.intros)
            by auto
          done
        apply(cases"e1 (the (s11 pn1)) = e2 (the (s12 pn2))")
        subgoal
          unfolding cond_gassn2_def
          apply auto
          apply(elim combine_blocks_waitE2)
             apply (auto simp add:assms)
          subgoal for tr'
            apply(rule interrupt_sol_cg.intros(1))
                apply auto
            subgoal
              apply(rule disj_gassn_disjI1)
              apply(rule sync_gassn.intros)
                    apply auto[4]
                prefer 3
                apply simp
              apply auto
              apply(rule interrupt_sol_cg.intros)
              apply auto
              done
              apply(rule merge_rdy_of_comm_specg2_prop'')
            apply(rule merge_inv.intros)
            by auto
          done
        by auto
      text \<open>case 1 - 2\<close>
      subgoal for tr1' a b p
        unfolding cond_gassn2_def
        apply auto
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        apply(rule sync_gassn.intros)
              apply auto
        apply(rule interrupt_sol_cg.intros(1))
        by auto
      text \<open>case 1 - 3\<close>
      subgoal for tr1' a1 b1 p1 j ch2 Q v tr2'
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply simp
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(cases"e1 (the (s11 pn1)) > e2 (the (s12 pn2))")
            subgoal
              unfolding cond_gassn2_def
              apply auto
              apply(rule interrupt_sol_cg.intros(3)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply(rule sync_gassn.intros)
                    apply auto
              apply(rule interrupt_sol_cg.intros(1))
              by auto
            apply(cases"e1 (the (s11 pn1)) < e2 (the (s12 pn2))")
            subgoal
              unfolding cond_gassn2_def
              apply auto
              apply(rule interrupt_sol_cg.intros(3)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply(rule sync_gassn.intros)
                    apply auto
              apply(rule interrupt_sol_cg.intros(1))
              by auto
            apply(cases"e1 (the (s11 pn1)) = e2 (the (s12 pn2))")
            subgoal
              unfolding cond_gassn2_def
              apply auto
              apply(rule interrupt_sol_cg.intros(3)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply(rule sync_gassn.intros)
                    apply auto
              apply(rule interrupt_sol_cg.intros(1))
              by auto
            by auto
          done
        done
      text \<open>case 1 - 4\<close>
      subgoal for tr1' a1 b1 p1 j ch2 Q d v tr2' a2 b2 p2
        apply(cases"e1 (the (s11 pn1)) > e2 (the (s12 pn2))")
        subgoal
          apply(elim combine_blocks_waitE4)
             apply(auto simp add:assms)
          subgoal 
            apply(cases "ch2\<in>chs")
            subgoal 
              by(elim combine_blocks_pairE2')
            apply(elim combine_blocks_unpairE3')
             apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                unfolding cond_gassn2_def
                apply auto
                apply(rule interrupt_sol_cg.intros(4)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(1))
                      apply auto
                  apply(rule)
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                apply(rule )
                by auto
              done
            done
          done
        apply(cases"e1 (the (s11 pn1)) < e2 (the (s12 pn2))")
        subgoal  
          apply(cases "d<e1 (the (s11 pn1))")
          subgoal
            apply(elim combine_blocks_waitE4)
             apply(auto simp add:assms)
            subgoal 
            apply(cases "ch2\<in>chs")
            subgoal 
              by(elim combine_blocks_pairE2')
            apply(elim combine_blocks_unpairE3')
             apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                unfolding cond_gassn2_def
                apply auto
                apply(rule interrupt_sol_cg.intros(4)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(1))
                      apply auto
                  apply(rule)
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                apply(rule )
                by auto
              done
            done
          done
        apply(cases "d>e1 (the (s11 pn1))")
          subgoal
            apply(elim combine_blocks_waitE3)
             apply(auto simp add:assms)
            subgoal for tr'
              unfolding cond_gassn2_def
              apply auto
              apply(rule interrupt_sol_cg.intros(1))
                  apply auto
              subgoal
                apply(rule sync_gassn.intros)
                      apply auto
                apply(rule interrupt_sol_cg.intros(4)[of j _ ch2])
                subgoal by auto
                     apply simp
                    apply auto
                apply(rule )
                by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                apply(rule merge_rdy_of_comm_specg2_prop'')
                apply(rule )
              by auto
            done
          apply(cases "d=e1 (the (s11 pn1))")
          subgoal
            apply(elim combine_blocks_waitE2')
             apply(auto simp add:assms)
            subgoal for tr'
              unfolding cond_gassn2_def
              apply auto
              apply(rule interrupt_sol_cg.intros(1))
                  apply auto
              subgoal
                apply(rule sync_gassn.intros)
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of j _ ch2])
                subgoal by auto
                     apply simp
                    by auto
                   apply(rule merge_rdy_of_comm_specg2_prop'')
                apply(rule )
              by auto
            done
          by auto
        apply(cases"e1 (the (s11 pn1)) = e2 (the (s12 pn2))")
        subgoal  
          apply(cases "d<e1 (the (s11 pn1))")
          subgoal
            apply(elim combine_blocks_waitE4)
             apply(auto simp add:assms)
            subgoal 
            apply(cases "ch2\<in>chs")
            subgoal 
              by(elim combine_blocks_pairE2')
            apply(elim combine_blocks_unpairE3')
             apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                unfolding cond_gassn2_def
                apply auto
                apply(rule interrupt_sol_cg.intros(4)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(1))
                      apply auto
                  apply(rule)
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                apply(rule )
                by auto
              done
            done
          done
        apply(cases "d=e1 (the (s11 pn1))")
          subgoal
            apply(elim combine_blocks_waitE2')
             apply(auto simp add:assms)
            subgoal for tr'
              unfolding cond_gassn2_def
              apply auto
              apply(rule interrupt_sol_cg.intros(1))
                  apply auto
              subgoal
                apply(rule disj_gassn_disjI1)
                apply(rule sync_gassn.intros)
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of j _ ch2])
                subgoal by auto
                     apply simp
                    by auto
                   apply(rule merge_rdy_of_comm_specg2_prop'')
                apply(rule )
              by auto
            done
          by auto
        by auto
      text \<open>case 1 - 5\<close>
      subgoal for tr1' a1 b1 p1 j ch2 Q v tr2'
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply simp
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(cases"e1 (the (s11 pn1)) > e2 (the (s12 pn2))")
            subgoal
              unfolding cond_gassn2_def
              apply auto
              apply(rule interrupt_sol_cg.intros(5)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply(rule sync_gassn.intros)
                    apply auto
              apply(rule interrupt_sol_cg.intros(1))
              by auto
            apply(cases"e1 (the (s11 pn1)) < e2 (the (s12 pn2))")
            subgoal
              unfolding cond_gassn2_def
              apply auto
              apply(rule interrupt_sol_cg.intros(5)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply(rule sync_gassn.intros)
                    apply auto
              apply(rule interrupt_sol_cg.intros(1))
              by auto
            apply(cases"e1 (the (s11 pn1)) = e2 (the (s12 pn2))")
            subgoal
              unfolding cond_gassn2_def
              apply auto
              apply(rule interrupt_sol_cg.intros(5)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply(rule sync_gassn.intros)
                    apply auto
              apply(rule interrupt_sol_cg.intros(1))
              by auto
            by auto
          done
        done
      text \<open>case 1 - 6\<close>
      subgoal for tr1' a1 b1 p1 j ch2 Q d v tr2' a2 b2 p2
        apply(cases"e1 (the (s11 pn1)) > e2 (the (s12 pn2))")
        subgoal
          apply(elim combine_blocks_waitE4)
             apply(auto simp add:assms)
          subgoal 
            apply(cases "ch2\<in>chs")
            subgoal 
              by(elim combine_blocks_pairE2')
            apply(elim combine_blocks_unpairE3')
             apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                unfolding cond_gassn2_def
                apply auto
                apply(rule interrupt_sol_cg.intros(6)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(1))
                      apply auto
                  apply(rule)
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                apply(rule )
                by auto
              done
            done
          done
        apply(cases"e1 (the (s11 pn1)) < e2 (the (s12 pn2))")
        subgoal  
          apply(cases "d<e1 (the (s11 pn1))")
          subgoal
            apply(elim combine_blocks_waitE4)
             apply(auto simp add:assms)
            subgoal 
            apply(cases "ch2\<in>chs")
            subgoal 
              by(elim combine_blocks_pairE2')
            apply(elim combine_blocks_unpairE3')
             apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                unfolding cond_gassn2_def
                apply auto
                apply(rule interrupt_sol_cg.intros(6)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(1))
                      apply auto
                  apply(rule)
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                apply(rule )
                by auto
              done
            done
          done
        apply(cases "d>e1 (the (s11 pn1))")
          subgoal
            apply(elim combine_blocks_waitE3)
             apply(auto simp add:assms)
            subgoal for tr'
              unfolding cond_gassn2_def
              apply auto
              apply(rule interrupt_sol_cg.intros(1))
                  apply auto
              subgoal
                apply(rule sync_gassn.intros)
                      apply auto
                apply(rule interrupt_sol_cg.intros(6)[of j _ ch2])
                subgoal by auto
                     apply simp
                    apply auto
                apply(rule )
                by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                apply(rule merge_rdy_of_comm_specg2_prop'')
                apply(rule )
              by auto
            done
          apply(cases "d=e1 (the (s11 pn1))")
          subgoal
            apply(elim combine_blocks_waitE2')
             apply(auto simp add:assms)
            subgoal for tr'
              unfolding cond_gassn2_def
              apply auto
              apply(rule interrupt_sol_cg.intros(1))
                  apply auto
              subgoal
                apply(rule sync_gassn.intros)
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of j _ ch2])
                subgoal by auto
                     apply simp
                    by auto
                   apply(rule merge_rdy_of_comm_specg2_prop'')
                apply(rule )
              by auto
            done
          by auto
        apply(cases"e1 (the (s11 pn1)) = e2 (the (s12 pn2))")
        subgoal  
          apply(cases "d<e1 (the (s11 pn1))")
          subgoal
            apply(elim combine_blocks_waitE4)
             apply(auto simp add:assms)
            subgoal 
            apply(cases "ch2\<in>chs")
            subgoal 
              by(elim combine_blocks_pairE2')
            apply(elim combine_blocks_unpairE3')
             apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                unfolding cond_gassn2_def
                apply auto
                apply(rule interrupt_sol_cg.intros(6)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(1))
                      apply auto
                  apply(rule)
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                apply(rule )
                by auto
              done
            done
          done
        apply(cases "d=e1 (the (s11 pn1))")
          subgoal
            apply(elim combine_blocks_waitE2')
             apply(auto simp add:assms)
            subgoal for tr'
              unfolding cond_gassn2_def
              apply auto
              apply(rule interrupt_sol_cg.intros(1))
                  apply auto
              subgoal
                apply(rule disj_gassn_disjI1)
                apply(rule sync_gassn.intros)
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of j _ ch2])
                subgoal by auto
                     apply simp
                    by auto
                   apply(rule merge_rdy_of_comm_specg2_prop'')
                apply(rule )
              by auto
            done
          by auto
        by auto
      text \<open>case 2 - 1\<close>
      subgoal for tr2' a2 b2 p2
        unfolding cond_gassn2_def
        apply auto
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        apply(rule sync_gassn.intros)
              apply auto
        apply(rule interrupt_sol_cg.intros(1))
        by auto
      text \<open>case 2 - 2\<close>
      subgoal 
        unfolding cond_gassn2_def
        apply auto
        subgoal
          apply(rule interrupt_sol_cg.intros(2))
           apply auto      
          apply(rule disj_gassn_disjI1)
          apply(rule sync_gassn.intros)
                apply auto
          apply(rule interrupt_sol_cg.intros(2))
          by auto
        done                  
      text \<open>case 2 - 3\<close>
      subgoal for i ch Q v tr2'
        unfolding cond_gassn2_def
        apply auto
        subgoal
          apply(rule interrupt_sol_cg.intros(2))
           apply auto
          apply(rule sync_gassn.intros)
              apply auto
          apply(rule interrupt_sol_cg.intros(3)[of i])
          subgoal by auto
          apply simp
        by auto
      subgoal
          apply(rule interrupt_sol_cg.intros(2))
         apply auto
        apply(rule disj_gassn_disjI1)
          apply(rule sync_gassn.intros)
              apply auto
          apply(rule interrupt_sol_cg.intros(3)[of i])
          subgoal by auto
          apply simp
          by auto
        subgoal
          apply(rule interrupt_sol_cg.intros(2))
         apply auto
        apply(rule disj_gassn_disjI1)
          apply(rule sync_gassn.intros)
              apply auto
          apply(rule interrupt_sol_cg.intros(3)[of i])
          subgoal by auto
          apply simp
          by auto
        done
      text \<open>case 2 - 4\<close>
      subgoal for i ch Q d' v tr2' a2 b2 p2
        unfolding cond_gassn2_def
        apply auto
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        apply(rule sync_gassn.intros)
              apply auto
        apply(rule interrupt_sol_cg.intros(4)[of i])
        subgoal by auto
        apply simp
        by auto
      text \<open>case 2 - 5\<close>
      subgoal for i ch Q v tr2'
        unfolding cond_gassn2_def
        apply auto
        subgoal
          apply(rule interrupt_sol_cg.intros(2))
           apply auto
          apply(rule sync_gassn.intros)
              apply auto
          apply(rule interrupt_sol_cg.intros(5)[of i])
          subgoal by auto
          apply simp
        by auto
      subgoal
          apply(rule interrupt_sol_cg.intros(2))
         apply auto
        apply(rule disj_gassn_disjI1)
          apply(rule sync_gassn.intros)
              apply auto
          apply(rule interrupt_sol_cg.intros(5)[of i])
          subgoal by auto
          apply simp
          by auto
        subgoal
          apply(rule interrupt_sol_cg.intros(2))
         apply auto
        apply(rule disj_gassn_disjI1)
          apply(rule sync_gassn.intros)
              apply auto
          apply(rule interrupt_sol_cg.intros(5)[of i])
          subgoal by auto
          apply simp
          by auto
        done
      text \<open>case 2 - 6\<close>
      subgoal for i ch Q d' v tr2' a2 b2 p2
        unfolding cond_gassn2_def
        apply auto
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        apply(rule sync_gassn.intros)
              apply auto
        apply(rule interrupt_sol_cg.intros(6)[of i])
        subgoal by auto
        apply simp
        by auto
      text \<open>case 3 - 1\<close>
      subgoal for i ch1 P v tr1' tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply simp
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(cases"e1 (the (s11 pn1)) > e2 (the (s12 pn2))")
            subgoal
              unfolding cond_gassn2_def
              apply auto
              apply(rule interrupt_sol_cg.intros(3)[of "k"])
              subgoal by auto
               apply simp
              apply(rule sync_gassn.intros)
                    apply auto
              apply(rule interrupt_sol_cg.intros(1))
              by auto
            apply(cases"e1 (the (s11 pn1)) < e2 (the (s12 pn2))")
            subgoal
              unfolding cond_gassn2_def
              apply auto
              apply(rule interrupt_sol_cg.intros(3)[of "k"])
              subgoal by auto
               apply simp
              apply(rule sync_gassn.intros)
                    apply auto
              apply(rule interrupt_sol_cg.intros(1))
              by auto
            apply(cases"e1 (the (s11 pn1)) = e2 (the (s12 pn2))")
            subgoal
              unfolding cond_gassn2_def
              apply auto
              apply(rule interrupt_sol_cg.intros(3)[of "k"])
              subgoal by auto
               apply simp
              apply(rule sync_gassn.intros)
                    apply auto
              apply(rule interrupt_sol_cg.intros(1))
              by auto
            by auto
          done
        done
      text \<open>case 3 - 2\<close>
      subgoal for i ch1 P v tr1'
        unfolding cond_gassn2_def
        apply auto
        subgoal
          apply(rule interrupt_sol_cg.intros(2))
           apply auto
          apply(rule sync_gassn.intros)
              apply auto
          apply(rule interrupt_sol_cg.intros(3)[of i])
          subgoal by auto
          apply simp
        by auto
      subgoal
          apply(rule interrupt_sol_cg.intros(2))
         apply auto
        apply(rule disj_gassn_disjI2)
          apply(rule sync_gassn.intros)
              apply auto
          apply(rule interrupt_sol_cg.intros(3)[of i])
          subgoal by auto
          apply simp
          by auto
        subgoal
          apply(rule interrupt_sol_cg.intros(2))
         apply auto
        apply(rule disj_gassn_disjI2)
          apply(rule sync_gassn.intros)
              apply auto
          apply(rule interrupt_sol_cg.intros(3)[of i])
          subgoal by auto
          apply simp
          by auto
        done
      text \<open>case 3 - 3\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases "e2 (the (s0 pn2)) < e1 (the (s0 pn1)) \<and> 0 < e1 (the (s0 pn1))")
        subgoal
          unfolding cond_gassn2_def
          apply auto
          apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE) by auto
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(3)[of "k"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(3)[of j])
                  subgoal by auto
                   apply simp
                  by auto
                done
              done
            done
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_unpairE1')
                apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(3)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(3)[of i])
                  subgoal by auto
                   apply simp
                  by auto
                done
              done
            subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(3)[of "k"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(3)[of j])
                  subgoal by auto
                   apply simp
                  by auto
                done
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(3)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(3)[of i])
                  subgoal by auto
                   apply simp
                  by auto
                done
              done
            done
          done
        apply(cases "e1 (the (s0 pn1)) < e2 (the (s0 pn2)) \<and> 0 < e2 (the (s0 pn2))")
        subgoal
          unfolding cond_gassn2_def
          apply auto
          apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE) by auto
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(3)[of "k"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(3)[of j])
                  subgoal by auto
                   apply simp
                  by auto
                done
              done
            done
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_unpairE1')
                apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(3)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(3)[of i])
                  subgoal by auto
                   apply simp
                  by auto
                done
              done
            subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(3)[of "k"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(3)[of j])
                  subgoal by auto
                   apply simp
                  by auto
                done
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(3)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(3)[of i])
                  subgoal by auto
                   apply simp
                  by auto
                done
              done
            done
          done
        subgoal
          apply(simp only:cond_gassn2_def)
          apply simp
          apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE) by auto
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto[2]
              subgoal premises pre for tr'
              proof-
                obtain k where kk:"comm_specg2_notin_chs specs1 chs ! k = InSpecg2 ch1 P \<and> k < length (comm_specg2_notin_chs specs1 chs)"
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(3)[of "k"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   prefer 2 
                   apply(rule interrupt_sol_cg.intros(3)[of j])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
            done
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_unpairE1')
                apply auto[2]
              subgoal premises pre for tr'
              proof-
                obtain k where kk:"comm_specg2_notin_chs specs2 chs ! k = InSpecg2 ch2 Q \<and> k < length (comm_specg2_notin_chs specs2 chs)"
                using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(3)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   apply(rule interrupt_sol_cg.intros(3)[of i])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
              subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto[2]
              subgoal premises pre for tr'
                proof-
                obtain k where kk:"comm_specg2_notin_chs specs1 chs ! k = InSpecg2 ch1 P \<and> k < length (comm_specg2_notin_chs specs1 chs)"
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(3)[of "k"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   prefer 2 
                   apply(rule interrupt_sol_cg.intros(3)[of j])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
              subgoal premises pre for tr'
                proof-
                obtain k where kk:"comm_specg2_notin_chs specs2 chs ! k = InSpecg2 ch2 Q \<and> k < length (comm_specg2_notin_chs specs2 chs)"
                using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(3)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   apply(rule interrupt_sol_cg.intros(3)[of i])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
              done
            done
          done
      text \<open>case 3 - 4\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
           apply auto
          subgoal for k
          apply(cases "e2 (the (s0 pn2)) < e1 (the (s0 pn1))")
          subgoal
            unfolding cond_gassn2_def
            apply auto
            apply(rule interrupt_sol_cg.intros(3)[of k])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(4)[of j])
            subgoal by auto
                 apply simp
            by auto
          apply(cases "e2 (the (s0 pn2)) > e1 (the (s0 pn1))")
          subgoal
            unfolding cond_gassn2_def
            apply auto
            apply(rule interrupt_sol_cg.intros(3)[of k])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(4)[of j])
            subgoal by auto
                 apply simp
            by auto
          apply(cases "e2 (the (s0 pn2)) = e1 (the (s0 pn1))")
          subgoal
            unfolding cond_gassn2_def
            apply auto
            apply(rule interrupt_sol_cg.intros(3)[of k])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(4)[of j])
            subgoal by auto
                 apply simp
              by auto
            by auto
          done
        done
      text \<open>case 3 - 5\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases "e2 (the (s0 pn2)) < e1 (the (s0 pn1)) \<and> 0 < e1 (the (s0 pn1))")
        subgoal
          unfolding cond_gassn2_def
          apply auto
          apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE) 
                apply auto
              using rdy_of_comm_specg2_prop1[of i specs1 ch1 P]
              using rdy_of_comm_specg2_prop2[of j specs2 ch2 Q]
              using assms
              apply auto
              by (smt (verit, ccfv_SIG) compat_rdy.elims(2) disjoint_iff fst_conv snd_conv)
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(3)[of "k"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(5)[of j])
                  subgoal by auto
                   apply simp
                  by auto
                done
              done
            done
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_unpairE1')
                apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(5)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(3)[of i])
                  subgoal by auto
                   apply simp
                  by auto
                done
              done
            subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(3)[of "k"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(5)[of j])
                  subgoal by auto
                   apply simp
                  by auto
                done
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(5)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(3)[of i])
                  subgoal by auto
                   apply simp
                  by auto
                done
              done
            done
          done
        apply(cases "e1 (the (s0 pn1)) < e2 (the (s0 pn2)) \<and> 0 < e2 (the (s0 pn2))")
        subgoal
          unfolding cond_gassn2_def
          apply auto
          apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE) 
                apply auto
              using rdy_of_comm_specg2_prop1[of i specs1 ch1 P]
              using rdy_of_comm_specg2_prop2[of j specs2 ch2 Q]
              using assms
              apply auto
              by (smt (verit, ccfv_SIG) compat_rdy.elims(2) disjoint_iff fst_conv snd_conv)
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(3)[of "k"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(5)[of j])
                  subgoal by auto
                   apply simp
                  by auto
                done
              done
            done
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_unpairE1')
                apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(5)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(3)[of i])
                  subgoal by auto
                   apply simp
                  by auto
                done
              done
            subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(3)[of "k"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(5)[of j])
                  subgoal by auto
                   apply simp
                  by auto
                done
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(5)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(3)[of i])
                  subgoal by auto
                   apply simp
                  by auto
                done
              done
            done
          done
        subgoal
          apply(simp only:cond_gassn2_def)
          apply simp
          apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE) 
                apply auto[2]
              using rdy_of_comm_specg2_prop1[of i specs1 ch1 P]
              using rdy_of_comm_specg2_prop2[of j specs2 ch2 Q]
              using assms
              by (smt (verit, ccfv_SIG) compat_rdy.elims(2) disjoint_iff fst_conv snd_conv)
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto[2]
              subgoal premises pre for tr'
              proof-
                obtain k where kk:"comm_specg2_notin_chs specs1 chs ! k = InSpecg2 ch1 P \<and> k < length (comm_specg2_notin_chs specs1 chs)"
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(3)[of "k"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   prefer 2 
                   apply(rule interrupt_sol_cg.intros(5)[of j])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
            done
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_unpairE1')
                apply auto[2]
              subgoal premises pre for tr'
              proof-
                obtain k where kk:"comm_specg2_notin_chs specs2 chs ! k = OutSpecg2 ch2 Q \<and> k < length (comm_specg2_notin_chs specs2 chs)"
                using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(5)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   apply(rule interrupt_sol_cg.intros(3)[of i])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
              subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto[2]
              subgoal premises pre for tr'
                proof-
                obtain k where kk:"comm_specg2_notin_chs specs1 chs ! k = InSpecg2 ch1 P \<and> k < length (comm_specg2_notin_chs specs1 chs)"
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(3)[of "k"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   prefer 2 
                   apply(rule interrupt_sol_cg.intros(5)[of j])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
              subgoal premises pre for tr'
                proof-
                obtain k where kk:"comm_specg2_notin_chs specs2 chs ! k = OutSpecg2 ch2 Q \<and> k < length (comm_specg2_notin_chs specs2 chs)"
                using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(5)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   apply(rule interrupt_sol_cg.intros(3)[of i])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
              done
            done
          done
      text \<open>case 3 - 6\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
           apply auto
          subgoal for k
          apply(cases "e2 (the (s0 pn2)) < e1 (the (s0 pn1))")
          subgoal
            unfolding cond_gassn2_def
            apply auto
            apply(rule interrupt_sol_cg.intros(3)[of k])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(6)[of j])
            subgoal by auto
                 apply simp
            by auto
          apply(cases "e2 (the (s0 pn2)) > e1 (the (s0 pn1))")
          subgoal
            unfolding cond_gassn2_def
            apply auto
            apply(rule interrupt_sol_cg.intros(3)[of k])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(6)[of j])
            subgoal by auto
                 apply simp
            by auto
          apply(cases "e2 (the (s0 pn2)) = e1 (the (s0 pn1))")
          subgoal
            unfolding cond_gassn2_def
            apply auto
            apply(rule interrupt_sol_cg.intros(3)[of k])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(6)[of j])
            subgoal by auto
                 apply simp
              by auto
            by auto
          done
        done
      text \<open>case 4 - 1\<close>
      subgoal for i ch1 P d v tr1' a1 b1 p1 tr2' a2 b2 p2
        apply(cases"e1 (the (s11 pn1)) < e2 (the (s12 pn2))")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply(auto simp add:assms)
          subgoal 
            apply(cases "ch1\<in>chs")
            subgoal 
              by(elim combine_blocks_pairE2)
            apply(elim combine_blocks_unpairE3)
             apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                unfolding cond_gassn2_def
                apply auto
                apply(rule interrupt_sol_cg.intros(4)[of "k"])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(1))
                      apply auto
                  apply(rule)
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                apply(rule )
                by auto
              done
            done
          done
        apply(cases"e1 (the (s11 pn1)) > e2 (the (s12 pn2))")
        subgoal  
          apply(cases "d<e2 (the (s12 pn2))")
          subgoal
            apply(elim combine_blocks_waitE3)
             apply(auto simp add:assms)
            subgoal 
            apply(cases "ch1\<in>chs")
            subgoal 
              by(elim combine_blocks_pairE2)
            apply(elim combine_blocks_unpairE3)
             apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                unfolding cond_gassn2_def
                apply auto
                apply(rule interrupt_sol_cg.intros(4)[of "k"])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(1))
                      apply auto
                  apply(rule)
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                apply(rule )
                by auto
              done
            done
          done
        apply(cases "d>e2 (the (s12 pn2))")
          subgoal
            apply(elim combine_blocks_waitE4)
             apply(auto simp add:assms)
            subgoal for tr'
              unfolding cond_gassn2_def
              apply auto
              apply(rule interrupt_sol_cg.intros(1))
                  apply auto
              subgoal
                apply(rule sync_gassn.intros)
                      apply auto
                apply(rule interrupt_sol_cg.intros(4)[of i _ ch1])
                subgoal by auto
                     apply simp
                    apply auto
                apply(rule )
                by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                apply(rule merge_rdy_of_comm_specg2_prop'')
                apply(rule )
              by auto
            done
          apply(cases "d=e2 (the (s12 pn2))")
          subgoal
            apply(elim combine_blocks_waitE2')
             apply(auto simp add:assms)
            subgoal for tr'
              unfolding cond_gassn2_def
              apply auto
              apply(rule interrupt_sol_cg.intros(1))
                  apply auto
              subgoal
                apply(rule sync_gassn.intros)
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of i _ ch1])
                subgoal by auto
                     apply simp
                    by auto
                   apply(rule merge_rdy_of_comm_specg2_prop'')
                apply(rule )
              by auto
            done
          by auto
        apply(cases"e1 (the (s11 pn1)) = e2 (the (s12 pn2))")
        subgoal  
          apply(cases "d<e2 (the (s12 pn2))")
          subgoal
            apply(elim combine_blocks_waitE3)
             apply(auto simp add:assms)
            subgoal 
            apply(cases "ch1\<in>chs")
            subgoal 
              by(elim combine_blocks_pairE2)
            apply(elim combine_blocks_unpairE3)
             apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                unfolding cond_gassn2_def
                apply auto
                apply(rule interrupt_sol_cg.intros(4)[of "k"])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(1))
                      apply auto
                  apply(rule)
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                apply(rule )
                by auto
              done
            done
          done
        apply(cases "d=e2 (the (s12 pn2))")
          subgoal
            apply(elim combine_blocks_waitE2')
             apply(auto simp add:assms)
            subgoal for tr'
              unfolding cond_gassn2_def
              apply auto
              apply(rule interrupt_sol_cg.intros(1))
                  apply auto
              subgoal
                apply(rule disj_gassn_disjI2)
                apply(rule sync_gassn.intros)
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of i _ ch1])
                subgoal by auto
                     apply simp
                    by auto
                   apply(rule merge_rdy_of_comm_specg2_prop'')
                apply(rule )
              by auto
            done
          by auto
        by auto
      text \<open>case 4 - 2\<close>
      subgoal for i ch1 P d v tr1' a1 b1 p1
        unfolding cond_gassn2_def
        apply auto
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        apply(rule sync_gassn.intros)
              apply auto
        apply(rule interrupt_sol_cg.intros(4)[of i])
        subgoal by auto
        apply simp
        by auto
      text \<open>case 4 - 3\<close>
      subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
           apply auto
          subgoal for k
          apply(cases "e2 (the (s0 pn2)) > e1 (the (s0 pn1))")
          subgoal
            unfolding cond_gassn2_def
            apply auto
            apply(rule interrupt_sol_cg.intros(3)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(4)[of i])
            subgoal by auto
                 apply simp
            by auto
          apply(cases "e2 (the (s0 pn2)) < e1 (the (s0 pn1))")
          subgoal
            unfolding cond_gassn2_def
            apply auto
            apply(rule interrupt_sol_cg.intros(3)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(4)[of i])
            subgoal by auto
                 apply simp
            by auto
          apply(cases "e2 (the (s0 pn2)) = e1 (the (s0 pn1))")
          subgoal
            unfolding cond_gassn2_def
            apply auto
            apply(rule interrupt_sol_cg.intros(3)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(4)[of i])
            subgoal by auto
                 apply simp
              by auto
            by auto
          done
        done                
      text \<open>case 4 - 4\<close>
      subgoal for i ch1 P d1 v1 tr1' a1 b1 p1 j ch2 Q d2 v2 tr2' a2 b2 p2
        apply(cases "d1<d2")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply (auto simp add: assms)
          apply(cases "ch1\<in>chs")
          subgoal by(elim combine_blocks_pairE2)
          apply(elim combine_blocks_unpairE3)
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              unfolding cond_gassn2_def
              apply auto
              subgoal
                apply(rule interrupt_sol_cg.intros(4)[of k])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(4)[of j])
                  subgoal by auto
                       apply simp
                      apply auto
                  apply(rule )
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                  apply(rule )
                by auto
              subgoal
                apply(rule interrupt_sol_cg.intros(4)[of k])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(4)[of j])
                  subgoal by auto
                       apply simp
                      apply auto
                  apply(rule )
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                  apply(rule )
                by auto
              subgoal
                apply(rule interrupt_sol_cg.intros(4)[of k])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(4)[of j])
                  subgoal by auto
                       apply simp
                      apply auto
                  apply(rule )
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                  apply(rule )
                by auto
              done
            done
          done
        apply(cases "d1>d2")
        subgoal
          apply(elim combine_blocks_waitE4)
             apply (auto simp add: assms)
          apply(cases "ch2\<in>chs")
          subgoal by(elim combine_blocks_pairE2')
          apply(elim combine_blocks_unpairE3')
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              unfolding cond_gassn2_def
              apply auto
              subgoal
                apply(rule interrupt_sol_cg.intros(4)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(4)[of i])
                  subgoal by auto
                       apply simp
                      apply auto
                  apply(rule )
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                  apply(rule )
                by auto
              subgoal
                apply(rule interrupt_sol_cg.intros(4)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(4)[of i])
                  subgoal by auto
                       apply simp
                      apply auto
                  apply(rule )
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                  apply(rule )
                by auto
              subgoal
                apply(rule interrupt_sol_cg.intros(4)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(4)[of i])
                  subgoal by auto
                       apply simp
                      apply auto
                  apply(rule )
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                  apply(rule )
                by auto
              done
            done
          done
        apply(cases "d1=d2")
        subgoal
          apply(elim combine_blocks_waitE2')
             apply (auto simp add: assms)
          apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE)
              by auto
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  unfolding cond_gassn2_def
                  apply auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(4)[of k])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(3)[of j])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(4)[of k])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(3)[of j])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(4)[of k])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(3)[of j])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  done
                done
              done
            done
          apply(cases "ch1\<in>chs")
          subgoal
            apply(elim combine_blocks_unpairE1')
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  unfolding cond_gassn2_def
                  apply auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(4)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(3)[of i])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(4)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(3)[of i])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(4)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(3)[of i])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  done
                done
              done
            subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  unfolding cond_gassn2_def
                  apply auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(4)[of k])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(3)[of j])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(4)[of k])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(3)[of j])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(4)[of k])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(3)[of j])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  done
                done
              subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  unfolding cond_gassn2_def
                  apply auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(4)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(3)[of i])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(4)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(3)[of i])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(4)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(3)[of i])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  done
                done
              done
            done
          by auto
      text \<open>case 4 - 5\<close>
      subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
           apply auto
          subgoal for k
          apply(cases "e2 (the (s0 pn2)) > e1 (the (s0 pn1))")
          subgoal
            unfolding cond_gassn2_def
            apply auto
            apply(rule interrupt_sol_cg.intros(5)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(4)[of i])
            subgoal by auto
                 apply simp
            by auto
          apply(cases "e2 (the (s0 pn2)) < e1 (the (s0 pn1))")
          subgoal
            unfolding cond_gassn2_def
            apply auto
            apply(rule interrupt_sol_cg.intros(5)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(4)[of i])
            subgoal by auto
                 apply simp
            by auto
          apply(cases "e2 (the (s0 pn2)) = e1 (the (s0 pn1))")
          subgoal
            unfolding cond_gassn2_def
            apply auto
            apply(rule interrupt_sol_cg.intros(5)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(4)[of i])
            subgoal by auto
                 apply simp
              by auto
            by auto
          done
        done     
      text \<open>case 4 - 6\<close>
      subgoal for i ch1 P d1 v1 tr1' a1 b1 p1 j ch2 Q d2 v2 tr2' a2 b2 p2
        apply(cases "d1<d2")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply (auto simp add: assms)
          apply(cases "ch1\<in>chs")
          subgoal by(elim combine_blocks_pairE2)
          apply(elim combine_blocks_unpairE3)
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              unfolding cond_gassn2_def
              apply auto
              subgoal
                apply(rule interrupt_sol_cg.intros(4)[of k])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(6)[of j])
                  subgoal by auto
                       apply simp
                      apply auto
                  apply(rule )
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                  apply(rule )
                by auto
              subgoal
                apply(rule interrupt_sol_cg.intros(4)[of k])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(6)[of j])
                  subgoal by auto
                       apply simp
                      apply auto
                  apply(rule )
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                  apply(rule )
                by auto
              subgoal
                apply(rule interrupt_sol_cg.intros(4)[of k])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(6)[of j])
                  subgoal by auto
                       apply simp
                      apply auto
                  apply(rule )
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                  apply(rule )
                by auto
              done
            done
          done
        apply(cases "d1>d2")
        subgoal
          apply(elim combine_blocks_waitE4)
             apply (auto simp add: assms)
          apply(cases "ch2\<in>chs")
          subgoal by(elim combine_blocks_pairE2')
          apply(elim combine_blocks_unpairE3')
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              unfolding cond_gassn2_def
              apply auto
              subgoal
                apply(rule interrupt_sol_cg.intros(6)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(4)[of i])
                  subgoal by auto
                       apply simp
                      apply auto
                  apply(rule )
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                  apply(rule )
                by auto
              subgoal
                apply(rule interrupt_sol_cg.intros(6)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(4)[of i])
                  subgoal by auto
                       apply simp
                      apply auto
                  apply(rule )
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                  apply(rule )
                by auto
              subgoal
                apply(rule interrupt_sol_cg.intros(6)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(4)[of i])
                  subgoal by auto
                       apply simp
                      apply auto
                  apply(rule )
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                  apply(rule )
                by auto
              done
            done
          done
        apply(cases "d1=d2")
        subgoal
          apply(elim combine_blocks_waitE2')
             apply (auto simp add: assms)
          apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE)
              apply auto[2]
              using rdy_of_comm_specg2_prop1[of i specs1 ch1 P]
              using rdy_of_comm_specg2_prop2[of j specs2 ch2 Q]
              using assms
              by (smt (verit, ccfv_SIG) compat_rdy.elims(2) disjoint_iff fst_conv snd_conv)
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  unfolding cond_gassn2_def
                  apply auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(4)[of k])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(5)[of j])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(4)[of k])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(5)[of j])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(4)[of k])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(5)[of j])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  done
                done
              done
            done
          apply(cases "ch1\<in>chs")
          subgoal
            apply(elim combine_blocks_unpairE1')
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  unfolding cond_gassn2_def
                  apply auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(6)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(3)[of i])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(6)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(3)[of i])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(6)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(3)[of i])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  done
                done
              done
            subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  unfolding cond_gassn2_def
                  apply auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(4)[of k])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(5)[of j])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(4)[of k])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(5)[of j])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(4)[of k])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(5)[of j])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  done
                done
              subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  unfolding cond_gassn2_def
                  apply auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(6)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(3)[of i])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(6)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(3)[of i])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(6)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(3)[of i])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  done
                done
              done
            done
          by auto
      text \<open>case 5 - 1\<close>
      subgoal for i ch1 P v tr1' tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply simp
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(cases"e1 (the (s11 pn1)) > e2 (the (s12 pn2))")
            subgoal
              unfolding cond_gassn2_def
              apply auto
              apply(rule interrupt_sol_cg.intros(5)[of "k"])
              subgoal by auto
               apply simp
              apply(rule sync_gassn.intros)
                    apply auto
              apply(rule interrupt_sol_cg.intros(1))
              by auto
            apply(cases"e1 (the (s11 pn1)) < e2 (the (s12 pn2))")
            subgoal
              unfolding cond_gassn2_def
              apply auto
              apply(rule interrupt_sol_cg.intros(5)[of "k"])
              subgoal by auto
               apply simp
              apply(rule sync_gassn.intros)
                    apply auto
              apply(rule interrupt_sol_cg.intros(1))
              by auto
            apply(cases"e1 (the (s11 pn1)) = e2 (the (s12 pn2))")
            subgoal
              unfolding cond_gassn2_def
              apply auto
              apply(rule interrupt_sol_cg.intros(5)[of "k"])
              subgoal by auto
               apply simp
              apply(rule sync_gassn.intros)
                    apply auto
              apply(rule interrupt_sol_cg.intros(1))
              by auto
            by auto
          done
        done
      text \<open>case 5 - 2\<close>
      subgoal for i ch1 P v tr1'
        unfolding cond_gassn2_def
        apply auto
        subgoal
          apply(rule interrupt_sol_cg.intros(2))
           apply auto
          apply(rule sync_gassn.intros)
              apply auto
          apply(rule interrupt_sol_cg.intros(5)[of i])
          subgoal by auto
          apply simp
        by auto
      subgoal
          apply(rule interrupt_sol_cg.intros(2))
         apply auto
        apply(rule disj_gassn_disjI2)
          apply(rule sync_gassn.intros)
              apply auto
          apply(rule interrupt_sol_cg.intros(5)[of i])
          subgoal by auto
          apply simp
          by auto
        subgoal
          apply(rule interrupt_sol_cg.intros(2))
         apply auto
        apply(rule disj_gassn_disjI2)
          apply(rule sync_gassn.intros)
              apply auto
          apply(rule interrupt_sol_cg.intros(5)[of i])
          subgoal by auto
          apply simp
          by auto
        done
      text \<open>case 5 - 3\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases "e2 (the (s0 pn2)) < e1 (the (s0 pn1)) \<and> 0 < e1 (the (s0 pn1))")
        subgoal
          unfolding cond_gassn2_def
          apply auto
          apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE) 
                apply auto[2]
              using rdy_of_comm_specg2_prop2[of i specs1 ch1 P]
              using rdy_of_comm_specg2_prop1[of j specs2 ch2 Q]
              using assms
              by (smt (verit, ccfv_SIG) compat_rdy.elims(2) disjoint_iff fst_conv snd_conv)
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(5)[of "k"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(3)[of j])
                  subgoal by auto
                   apply simp
                  by auto
                done
              done
            done
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_unpairE1')
                apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(3)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(5)[of i])
                  subgoal by auto
                   apply simp
                  by auto
                done
              done
            subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(5)[of "k"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(3)[of j])
                  subgoal by auto
                   apply simp
                  by auto
                done
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(3)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(5)[of i])
                  subgoal by auto
                   apply simp
                  by auto
                done
              done
            done
          done
        apply(cases "e1 (the (s0 pn1)) < e2 (the (s0 pn2)) \<and> 0 < e2 (the (s0 pn2))")
        subgoal
          unfolding cond_gassn2_def
          apply auto
          apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE) 
                apply auto[2]
              using rdy_of_comm_specg2_prop2[of i specs1 ch1 P]
              using rdy_of_comm_specg2_prop1[of j specs2 ch2 Q]
              using assms
              by (smt (verit, ccfv_SIG) compat_rdy.elims(2) disjoint_iff fst_conv snd_conv)
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(5)[of "k"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(3)[of j])
                  subgoal by auto
                   apply simp
                  by auto
                done
              done
            done
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_unpairE1')
                apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(3)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(5)[of i])
                  subgoal by auto
                   apply simp
                  by auto
                done
              done
            subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(5)[of "k"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(3)[of j])
                  subgoal by auto
                   apply simp
                  by auto
                done
              subgoal for tr'
                using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(3)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(5)[of i])
                  subgoal by auto
                   apply simp
                  by auto
                done
              done
            done
          done
        subgoal
          apply(simp only:cond_gassn2_def)
          apply simp
          apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE) 
                apply auto[2]
              using rdy_of_comm_specg2_prop2[of i specs1 ch1 P]
              using rdy_of_comm_specg2_prop1[of j specs2 ch2 Q]
              using assms
              by (smt (verit, ccfv_SIG) compat_rdy.elims(2) disjoint_iff fst_conv snd_conv)
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto[2]
              subgoal premises pre for tr'
              proof-
                obtain k where kk:"comm_specg2_notin_chs specs1 chs ! k = OutSpecg2 ch1 P \<and> k < length (comm_specg2_notin_chs specs1 chs)"
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(5)[of "k"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   prefer 2 
                   apply(rule interrupt_sol_cg.intros(3)[of j])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
            done
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_unpairE1')
                apply auto[2]
              subgoal premises pre for tr'
              proof-
                obtain k where kk:"comm_specg2_notin_chs specs2 chs ! k = InSpecg2 ch2 Q \<and> k < length (comm_specg2_notin_chs specs2 chs)"
                using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(3)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   apply(rule interrupt_sol_cg.intros(5)[of i])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
              subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto[2]
              subgoal premises pre for tr'
                proof-
                obtain k where kk:"comm_specg2_notin_chs specs1 chs ! k = OutSpecg2 ch1 P \<and> k < length (comm_specg2_notin_chs specs1 chs)"
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(5)[of "k"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   prefer 2 
                   apply(rule interrupt_sol_cg.intros(3)[of j])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
              subgoal premises pre for tr'
                proof-
                obtain k where kk:"comm_specg2_notin_chs specs2 chs ! k = InSpecg2 ch2 Q \<and> k < length (comm_specg2_notin_chs specs2 chs)"
                using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(3)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   apply(rule interrupt_sol_cg.intros(5)[of i])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
              done
            done
          done
      text \<open>case 5 - 4\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
           apply auto
          subgoal for k
          apply(cases "e2 (the (s0 pn2)) < e1 (the (s0 pn1))")
          subgoal
            unfolding cond_gassn2_def
            apply auto
            apply(rule interrupt_sol_cg.intros(5)[of k])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(4)[of j])
            subgoal by auto
                 apply simp
            by auto
          apply(cases "e2 (the (s0 pn2)) > e1 (the (s0 pn1))")
          subgoal
            unfolding cond_gassn2_def
            apply auto
            apply(rule interrupt_sol_cg.intros(5)[of k])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(4)[of j])
            subgoal by auto
                 apply simp
            by auto
          apply(cases "e2 (the (s0 pn2)) = e1 (the (s0 pn1))")
          subgoal
            unfolding cond_gassn2_def
            apply auto
            apply(rule interrupt_sol_cg.intros(5)[of k])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(4)[of j])
            subgoal by auto
                 apply simp
              by auto
            by auto
          done
        done
      text \<open>case 5 - 5\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases "e2 (the (s0 pn2)) < e1 (the (s0 pn1)) \<and> 0 < e1 (the (s0 pn1))")
        subgoal
          unfolding cond_gassn2_def
          apply auto
          apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE) 
              by auto
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(5)[of "k"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(5)[of j])
                  subgoal by auto
                   apply simp
                  by auto
                done
              done
            done
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_unpairE1')
                apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(5)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(5)[of i])
                  subgoal by auto
                   apply simp
                  by auto
                done
              done
            subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(5)[of "k"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(5)[of j])
                  subgoal by auto
                   apply simp
                  by auto
                done
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(5)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(5)[of i])
                  subgoal by auto
                   apply simp
                  by auto
                done
              done
            done
          done
        apply(cases "e1 (the (s0 pn1)) < e2 (the (s0 pn2)) \<and> 0 < e2 (the (s0 pn2))")
        subgoal
          unfolding cond_gassn2_def
          apply auto
          apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE) 
              by auto
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(5)[of "k"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(5)[of j])
                  subgoal by auto
                   apply simp
                  by auto
                done
              done
            done
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_unpairE1')
                apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(5)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(5)[of i])
                  subgoal by auto
                   apply simp
                  by auto
                done
              done
            subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(5)[of "k"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(5)[of j])
                  subgoal by auto
                   apply simp
                  by auto
                done
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  apply(rule interrupt_sol_cg.intros(5)[of "k + length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal by auto
                   apply simp
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(5)[of i])
                  subgoal by auto
                   apply simp
                  by auto
                done
              done
            done
          done
        subgoal
          apply(simp only:cond_gassn2_def)
          apply simp
          apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE) 
              by auto
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto[2]
              subgoal premises pre for tr'
              proof-
                obtain k where kk:"comm_specg2_notin_chs specs1 chs ! k = OutSpecg2 ch1 P \<and> k < length (comm_specg2_notin_chs specs1 chs)"
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(5)[of "k"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   prefer 2 
                   apply(rule interrupt_sol_cg.intros(5)[of j])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
            done
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_unpairE1')
                apply auto[2]
              subgoal premises pre for tr'
              proof-
                obtain k where kk:"comm_specg2_notin_chs specs2 chs ! k = OutSpecg2 ch2 Q \<and> k < length (comm_specg2_notin_chs specs2 chs)"
                using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(5)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   apply(rule interrupt_sol_cg.intros(5)[of i])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
              subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto[2]
              subgoal premises pre for tr'
                proof-
                obtain k where kk:"comm_specg2_notin_chs specs1 chs ! k = OutSpecg2 ch1 P \<and> k < length (comm_specg2_notin_chs specs1 chs)"
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(5)[of "k"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   prefer 2 
                   apply(rule interrupt_sol_cg.intros(5)[of j])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
              subgoal premises pre for tr'
                proof-
                obtain k where kk:"comm_specg2_notin_chs specs2 chs ! k = OutSpecg2 ch2 Q \<and> k < length (comm_specg2_notin_chs specs2 chs)"
                using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs] pre
                by auto
              show ?thesis
                apply(simp add: pre)
                  apply(rule interrupt_sol_cg.intros(5)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                  subgoal using kk by auto
                   apply (simp add:kk)
                  apply(rule sync_gassn.intros)
                        apply (auto simp add: pre)
                  prefer 3
                  using pre apply simp
                   apply(rule interrupt_sol_cg.intros(5)[of i])
                  subgoal using kk pre  by auto
                  using pre apply simp
                  using pre
                  by auto
              qed
                done
              done
            done
          done
      text \<open>case 5 - 6\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
           apply auto
          subgoal for k
          apply(cases "e2 (the (s0 pn2)) < e1 (the (s0 pn1))")
          subgoal
            unfolding cond_gassn2_def
            apply auto
            apply(rule interrupt_sol_cg.intros(5)[of k])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(6)[of j])
            subgoal by auto
                 apply simp
            by auto
          apply(cases "e2 (the (s0 pn2)) > e1 (the (s0 pn1))")
          subgoal
            unfolding cond_gassn2_def
            apply auto
            apply(rule interrupt_sol_cg.intros(5)[of k])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(6)[of j])
            subgoal by auto
                 apply simp
            by auto
          apply(cases "e2 (the (s0 pn2)) = e1 (the (s0 pn1))")
          subgoal
            unfolding cond_gassn2_def
            apply auto
            apply(rule interrupt_sol_cg.intros(5)[of k])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(6)[of j])
            subgoal by auto
                 apply simp
              by auto
            by auto
          done
        done
      text \<open>case 6 - 1\<close>
      subgoal for i ch1 P d v tr1' a1 b1 p1 tr2' a2 b2 p2
        apply(cases"e1 (the (s11 pn1)) < e2 (the (s12 pn2))")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply(auto simp add:assms)
          subgoal 
            apply(cases "ch1\<in>chs")
            subgoal 
              by(elim combine_blocks_pairE2)
            apply(elim combine_blocks_unpairE3)
             apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                unfolding cond_gassn2_def
                apply auto
                apply(rule interrupt_sol_cg.intros(6)[of "k"])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(1))
                      apply auto
                  apply(rule)
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                apply(rule )
                by auto
              done
            done
          done
        apply(cases"e1 (the (s11 pn1)) > e2 (the (s12 pn2))")
        subgoal  
          apply(cases "d<e2 (the (s12 pn2))")
          subgoal
            apply(elim combine_blocks_waitE3)
             apply(auto simp add:assms)
            subgoal 
            apply(cases "ch1\<in>chs")
            subgoal 
              by(elim combine_blocks_pairE2)
            apply(elim combine_blocks_unpairE3)
             apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                unfolding cond_gassn2_def
                apply auto
                apply(rule interrupt_sol_cg.intros(6)[of "k"])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(1))
                      apply auto
                  apply(rule)
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                apply(rule )
                by auto
              done
            done
          done
        apply(cases "d>e2 (the (s12 pn2))")
          subgoal
            apply(elim combine_blocks_waitE4)
             apply(auto simp add:assms)
            subgoal for tr'
              unfolding cond_gassn2_def
              apply auto
              apply(rule interrupt_sol_cg.intros(1))
                  apply auto
              subgoal
                apply(rule sync_gassn.intros)
                      apply auto
                apply(rule interrupt_sol_cg.intros(6)[of i _ ch1])
                subgoal by auto
                     apply simp
                    apply auto
                apply(rule )
                by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                apply(rule merge_rdy_of_comm_specg2_prop'')
                apply(rule )
              by auto
            done
          apply(cases "d=e2 (the (s12 pn2))")
          subgoal
            apply(elim combine_blocks_waitE2')
             apply(auto simp add:assms)
            subgoal for tr'
              unfolding cond_gassn2_def
              apply auto
              apply(rule interrupt_sol_cg.intros(1))
                  apply auto
              subgoal
                apply(rule sync_gassn.intros)
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of i _ ch1])
                subgoal by auto
                     apply simp
                    by auto
                   apply(rule merge_rdy_of_comm_specg2_prop'')
                apply(rule )
              by auto
            done
          by auto
        apply(cases"e1 (the (s11 pn1)) = e2 (the (s12 pn2))")
        subgoal  
          apply(cases "d<e2 (the (s12 pn2))")
          subgoal
            apply(elim combine_blocks_waitE3)
             apply(auto simp add:assms)
            subgoal 
            apply(cases "ch1\<in>chs")
            subgoal 
              by(elim combine_blocks_pairE2)
            apply(elim combine_blocks_unpairE3)
             apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                unfolding cond_gassn2_def
                apply auto
                apply(rule interrupt_sol_cg.intros(6)[of "k"])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(1))
                      apply auto
                  apply(rule)
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                apply(rule )
                by auto
              done
            done
          done
        apply(cases "d=e2 (the (s12 pn2))")
          subgoal
            apply(elim combine_blocks_waitE2')
             apply(auto simp add:assms)
            subgoal for tr'
              unfolding cond_gassn2_def
              apply auto
              apply(rule interrupt_sol_cg.intros(1))
                  apply auto
              subgoal
                apply(rule disj_gassn_disjI2)
                apply(rule sync_gassn.intros)
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of i _ ch1])
                subgoal by auto
                     apply simp
                    by auto
                   apply(rule merge_rdy_of_comm_specg2_prop'')
                apply(rule )
              by auto
            done
          by auto
        by auto
      text \<open>case 6 - 2\<close>
      subgoal for i ch1 P d v tr1' a1 b1 p1
        unfolding cond_gassn2_def
        apply auto
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        apply(rule sync_gassn.intros)
              apply auto
        apply(rule interrupt_sol_cg.intros(6)[of i])
        subgoal by auto
        apply simp
        by auto
      text \<open>case 6 - 3\<close>
      subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
           apply auto
          subgoal for k
          apply(cases "e2 (the (s0 pn2)) > e1 (the (s0 pn1))")
          subgoal
            unfolding cond_gassn2_def
            apply auto
            apply(rule interrupt_sol_cg.intros(3)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(6)[of i])
            subgoal by auto
                 apply simp
            by auto
          apply(cases "e2 (the (s0 pn2)) < e1 (the (s0 pn1))")
          subgoal
            unfolding cond_gassn2_def
            apply auto
            apply(rule interrupt_sol_cg.intros(3)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(6)[of i])
            subgoal by auto
                 apply simp
            by auto
          apply(cases "e2 (the (s0 pn2)) = e1 (the (s0 pn1))")
          subgoal
            unfolding cond_gassn2_def
            apply auto
            apply(rule interrupt_sol_cg.intros(3)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(6)[of i])
            subgoal by auto
                 apply simp
              by auto
            by auto
          done
        done                
      text \<open>case 6 - 4\<close>
      subgoal for i ch1 P d1 v1 tr1' a1 b1 p1 j ch2 Q d2 v2 tr2' a2 b2 p2
        apply(cases "d1<d2")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply (auto simp add: assms)
          apply(cases "ch1\<in>chs")
          subgoal by(elim combine_blocks_pairE2)
          apply(elim combine_blocks_unpairE3)
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              unfolding cond_gassn2_def
              apply auto
              subgoal
                apply(rule interrupt_sol_cg.intros(6)[of k])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(4)[of j])
                  subgoal by auto
                       apply simp
                      apply auto
                  apply(rule )
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                  apply(rule )
                by auto
              subgoal
                apply(rule interrupt_sol_cg.intros(6)[of k])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(4)[of j])
                  subgoal by auto
                       apply simp
                      apply auto
                  apply(rule )
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                  apply(rule )
                by auto
              subgoal
                apply(rule interrupt_sol_cg.intros(6)[of k])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(4)[of j])
                  subgoal by auto
                       apply simp
                      apply auto
                  apply(rule )
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                  apply(rule )
                by auto
              done
            done
          done
        apply(cases "d1>d2")
        subgoal
          apply(elim combine_blocks_waitE4)
             apply (auto simp add: assms)
          apply(cases "ch2\<in>chs")
          subgoal by(elim combine_blocks_pairE2')
          apply(elim combine_blocks_unpairE3')
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              unfolding cond_gassn2_def
              apply auto
              subgoal
                apply(rule interrupt_sol_cg.intros(4)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(6)[of i])
                  subgoal by auto
                       apply simp
                      apply auto
                  apply(rule )
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                  apply(rule )
                by auto
              subgoal
                apply(rule interrupt_sol_cg.intros(4)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(6)[of i])
                  subgoal by auto
                       apply simp
                      apply auto
                  apply(rule )
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                  apply(rule )
                by auto
              subgoal
                apply(rule interrupt_sol_cg.intros(4)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(6)[of i])
                  subgoal by auto
                       apply simp
                      apply auto
                  apply(rule )
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                  apply(rule )
                by auto
              done
            done
          done
        apply(cases "d1=d2")
        subgoal
          apply(elim combine_blocks_waitE2')
             apply (auto simp add: assms)
          apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE)
              apply auto[2]
              using rdy_of_comm_specg2_prop2[of i specs1 ch1 P]
              using rdy_of_comm_specg2_prop1[of j specs2 ch2 Q]
              using assms
              by (smt (verit, ccfv_SIG) compat_rdy.elims(2) disjoint_iff fst_conv snd_conv)
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  unfolding cond_gassn2_def
                  apply auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(6)[of k])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(3)[of j])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(6)[of k])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(3)[of j])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(6)[of k])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(3)[of j])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  done
                done
              done
            done
          apply(cases "ch1\<in>chs")
          subgoal
            apply(elim combine_blocks_unpairE1')
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  unfolding cond_gassn2_def
                  apply auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(4)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(5)[of i])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(4)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(5)[of i])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(4)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(5)[of i])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  done
                done
              done
            subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  unfolding cond_gassn2_def
                  apply auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(6)[of k])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(3)[of j])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(6)[of k])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(3)[of j])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(6)[of k])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(3)[of j])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  done
                done
              subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  unfolding cond_gassn2_def
                  apply auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(4)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(5)[of i])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(4)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(5)[of i])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(4)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(5)[of i])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  done
                done
              done
            done
          by auto
      text \<open>case 6 - 5\<close>
      subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
           apply auto
          subgoal for k
          apply(cases "e2 (the (s0 pn2)) > e1 (the (s0 pn1))")
          subgoal
            unfolding cond_gassn2_def
            apply auto
            apply(rule interrupt_sol_cg.intros(5)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(6)[of i])
            subgoal by auto
                 apply simp
            by auto
          apply(cases "e2 (the (s0 pn2)) < e1 (the (s0 pn1))")
          subgoal
            unfolding cond_gassn2_def
            apply auto
            apply(rule interrupt_sol_cg.intros(5)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(6)[of i])
            subgoal by auto
                 apply simp
            by auto
          apply(cases "e2 (the (s0 pn2)) = e1 (the (s0 pn1))")
          subgoal
            unfolding cond_gassn2_def
            apply auto
            apply(rule interrupt_sol_cg.intros(5)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply(rule sync_gassn.intros)
                  apply auto
            apply(rule interrupt_sol_cg.intros(6)[of i])
            subgoal by auto
                 apply simp
              by auto
            by auto
          done
        done     
      text \<open>case 6 - 6\<close>
      subgoal for i ch1 P d1 v1 tr1' a1 b1 p1 j ch2 Q d2 v2 tr2' a2 b2 p2
        apply(cases "d1<d2")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply (auto simp add: assms)
          apply(cases "ch1\<in>chs")
          subgoal by(elim combine_blocks_pairE2)
          apply(elim combine_blocks_unpairE3)
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              unfolding cond_gassn2_def
              apply auto
              subgoal
                apply(rule interrupt_sol_cg.intros(6)[of k])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(6)[of j])
                  subgoal by auto
                       apply simp
                      apply auto
                  apply(rule )
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                  apply(rule )
                by auto
              subgoal
                apply(rule interrupt_sol_cg.intros(6)[of k])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(6)[of j])
                  subgoal by auto
                       apply simp
                      apply auto
                  apply(rule )
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                  apply(rule )
                by auto
              subgoal
                apply(rule interrupt_sol_cg.intros(6)[of k])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(6)[of j])
                  subgoal by auto
                       apply simp
                      apply auto
                  apply(rule )
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                  apply(rule )
                by auto
              done
            done
          done
        apply(cases "d1>d2")
        subgoal
          apply(elim combine_blocks_waitE4)
             apply (auto simp add: assms)
          apply(cases "ch2\<in>chs")
          subgoal by(elim combine_blocks_pairE2')
          apply(elim combine_blocks_unpairE3')
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              unfolding cond_gassn2_def
              apply auto
              subgoal
                apply(rule interrupt_sol_cg.intros(6)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(6)[of i])
                  subgoal by auto
                       apply simp
                      apply auto
                  apply(rule )
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                  apply(rule )
                by auto
              subgoal
                apply(rule interrupt_sol_cg.intros(6)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(6)[of i])
                  subgoal by auto
                       apply simp
                      apply auto
                  apply(rule )
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                  apply(rule )
                by auto
              subgoal
                apply(rule interrupt_sol_cg.intros(6)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                     apply simp
                    apply auto
                subgoal
                  apply(rule sync_gassn.intros)
                        apply auto
                  apply(rule interrupt_sol_cg.intros(6)[of i])
                  subgoal by auto
                       apply simp
                      apply auto
                  apply(rule )
                  by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
                 apply(rule merge_rdy_of_comm_specg2_prop'')
                  apply(rule )
                by auto
              done
            done
          done
        apply(cases "d1=d2")
        subgoal
          apply(elim combine_blocks_waitE2')
             apply (auto simp add: assms)
          apply(cases "ch2\<in>chs")
          subgoal
            apply(cases "ch1\<in>chs")
            subgoal
              apply(elim combine_blocks_pairE)
              by auto
            subgoal
              apply(elim combine_blocks_unpairE1)
                apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  unfolding cond_gassn2_def
                  apply auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(6)[of k])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(5)[of j])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(6)[of k])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(5)[of j])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(6)[of k])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(5)[of j])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  done
                done
              done
            done
          apply(cases "ch1\<in>chs")
          subgoal
            apply(elim combine_blocks_unpairE1')
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  unfolding cond_gassn2_def
                  apply auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(6)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(5)[of i])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(6)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(5)[of i])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(6)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(5)[of i])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  done
                done
              done
            subgoal
              apply(elim combine_blocks_unpairE2)
                 apply auto
              subgoal for tr'
                using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
                apply auto
                subgoal for k
                  unfolding cond_gassn2_def
                  apply auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(6)[of k])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(5)[of j])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(6)[of k])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(5)[of j])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(6)[of k])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(5)[of j])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  done
                done
              subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
                apply auto
                subgoal for k
                  unfolding cond_gassn2_def
                  apply auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(6)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(5)[of i])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(6)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(5)[of i])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  subgoal
                    apply(rule interrupt_sol_cg.intros(6)[of "k+length (comm_specg2_notin_chs specs1 chs)"])
                    subgoal by auto
                         apply simp
                        apply auto
                    subgoal
                      apply(rule sync_gassn.intros)
                      apply auto
                      apply(rule interrupt_sol_cg.intros(5)[of i])
                      subgoal by auto
                       apply simp
                      by auto
                     apply(rule merge_rdy_of_comm_specg2_prop'')
                    apply(rule )
                    by auto
                  done
                done
              done
            done
          by auto
        done
      done
    done


thm sync_gassn_interrupt_solInf_interrupt_solInf2
thm sync_gassn_interrupt_sol_interrupt_sol1

lemma sync_gassn_interrupt_sol_interrupt_sol2:
  assumes "\<not>compat_rdy (rdy_of_comm_specg2 specs1) (rdy_of_comm_specg2 specs2)" 
     and  "pn1 \<in> pns1 \<and> pn2 \<in> pns2 \<and> pns1 \<inter> pns2 = {}"
shows
  "sync_gassn chs pns1 pns2 (interrupt_sol_cg I1 pn1 e1 G1 specs1) (interrupt_sol_cg I2 pn2 e2 G2 specs2) s0 \<Longrightarrow>\<^sub>G
   interrupt_sol_cg (merge_inv I1 I2) pp (\<lambda>_ .0) 
         (\<lambda>_ . IFG  (\<lambda>s0. e1 (the (s0 pn1)) > 0) 
               THEN (IFG (\<lambda> s0. e2 (the (s0 pn2)) > 0)
                     THEN com_of_specs22_sync chs pns1 pns2 (com_of_specs2 chs specs1 specs2)
                     ELSE (com_of_specs22_sync chs pns1 pns2 (com_of_specs2 chs specs1 specs2) 
                            \<or>\<^sub>g sync_gassn chs pns1 pns2 (interrupt_sol_cg I1 pn1 e1 G1 specs1) (G2 0))
                     FI)
               ELSE (IFG (\<lambda> s0. e2 (the (s0 pn2)) > 0)
                     THEN (com_of_specs22_sync chs pns1 pns2 (com_of_specs2 chs specs1 specs2) 
                            \<or>\<^sub>g sync_gassn chs pns1 pns2 (G1 0) (interrupt_sol_cg I2 pn2 e2 G2 specs2))
                     ELSE (com_of_specs22_sync chs pns1 pns2 (com_of_specs2 chs specs1 specs2) 
                            \<or>\<^sub>g sync_gassn chs pns1 pns2 (interrupt_sol_cg I1 pn1 e1 G1 specs1) (G2 0)
                            \<or>\<^sub>g sync_gassn chs pns1 pns2 (G1 0) (interrupt_sol_cg I2 pn2 e2 G2 specs2))
                     FI)
               FI)
          ((map (if1 chs pns1 pns2 I2 pn2 e2 G2 specs2) (comm_specg2_notin_chs specs1 chs))@  
           (map (if2 chs pns1 pns2 I1 pn1 e1 G1 specs1) (comm_specg2_notin_chs specs2 chs))) s0"
unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply(subgoal_tac"e1 (the (s0 pn1)) = e1 (the (s11 pn1))")
       prefer 2
      subgoal 
        apply auto
        apply(subst merge_state_eval1[of pn1]) using assms by auto
      apply(subgoal_tac"e2 (the (s0 pn2)) = e2 (the (s12 pn2))")
       prefer 2
      subgoal 
        apply auto
        apply(subst merge_state_eval2[of pn2]) using assms by auto
      apply (elim interrupt_sol_cg.cases) apply auto
      text \<open>case 1 - 1\<close>
      subgoal for tr1' a1 b1 p1 tr2' a2 b2 p2
        apply(elim combine_blocks_waitE1)
        using assms by simp
      text \<open>case 1 - 2\<close>
      subgoal for tr1' a1 b1 p1
        apply(rule interrupt_sol_cg.intros(2))
         apply simp
        unfolding cond_gassn2_def
        apply auto
        apply(rule disj_gassn_disjI2)
        apply(rule )
              apply auto
        apply(rule interrupt_sol_cg.intros(1))
        by auto
      text \<open>case 1 - 3\<close>
      subgoal for tr1' a1 b1 p1 j ch2 Q v tr2'
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(1))
            by auto
          done
        done
      text \<open>case 1 - 4\<close>
      subgoal for tr1' a1 b1 p1
        apply(elim combine_blocks_waitE1)
        using assms by simp
      text \<open>case 1 - 5\<close>
      subgoal for tr1' a1 b1 p1 j ch2 Q v tr2'
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(1))
            by auto
          done
        done
      text \<open>case 1 - 6\<close>
      subgoal for tr1' a1 b1 p1
        apply(elim combine_blocks_waitE1)
        using assms by simp
      text \<open>case 2 - 1\<close>
      subgoal for tr2' a2 b2 p2
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def 
        apply auto
        apply(rule disj_gassn_disjI2)
        apply rule
              apply auto
        apply(rule interrupt_sol_cg.intros(1))
        by auto
      text \<open>case 2 - 2\<close>
      subgoal
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def 
        apply auto
        apply(rule disj_gassn_disjI2)
        apply(rule disj_gassn_disjI2)
        apply rule
              apply auto
        apply(rule )
        by auto
      text \<open>case 2 - 3\<close>
      subgoal for j ch2 Q v tr2'
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def 
        apply auto
        subgoal
          apply(rule disj_gassn_disjI2)
          apply rule
                apply auto
          apply(rule )
          by simp
        subgoal
          apply(rule disj_gassn_disjI2)
          apply(rule disj_gassn_disjI2)
          apply rule
                apply auto
          apply rule
          by simp
        done
      text \<open>case 2 - 4\<close>
      subgoal for j ch2 Q d v tr2' a2 b2 p2
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def 
        apply auto
        apply(rule disj_gassn_disjI2)
        apply rule
              apply auto
        apply(rule interrupt_sol_cg.intros(4)[of j])
        subgoal by auto
        apply simp
        by auto
      text \<open>case 2 - 5\<close>
      subgoal for j ch2 Q v tr2'
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def 
        apply auto
        subgoal
          apply(rule disj_gassn_disjI2)
          apply rule
                apply auto
          apply(rule )
          by simp
        subgoal
          apply(rule disj_gassn_disjI2)
          apply(rule disj_gassn_disjI2)
          apply rule
                apply auto
          apply rule
          by simp
        done
      text \<open>case 2 - 6\<close>
      subgoal for j ch2 Q d v tr2' a2 b2 p2
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def 
        apply auto
        apply(rule disj_gassn_disjI2)
        apply rule
              apply auto
        apply(rule interrupt_sol_cg.intros(6)[of j])
        subgoal by auto
        apply simp
        by auto
      text \<open>case 3 - 1\<close>
      subgoal for i ch1 P v tr1' tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(3)[of "k"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(1))
            by auto
          done
        done
      text \<open>case 3 - 2\<close>
      subgoal for i ch1 P v tr1'
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def 
        apply auto
        subgoal
          apply(rule disj_gassn_disjI2)
          apply rule
                apply auto
          apply(rule )
          by simp
        subgoal
          apply(rule disj_gassn_disjI2)
          apply(rule disj_gassn_disjI1)
          apply rule
                apply auto
          apply rule
          by simp
        done
      text \<open>case 3 - 3\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases"ch2\<in>chs")
        subgoal
          apply(cases"ch1\<in>chs")
          subgoal 
            apply(elim combine_blocks_pairE)
            by auto
          subgoal
            apply(elim combine_blocks_unpairE1)
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of k])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of j])
                subgoal by auto
                 apply simp
                by auto
              done
            done
          done
        subgoal
          apply(cases "ch1\<in>chs")
          subgoal
            apply(elim combine_blocks_unpairE1')
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of i])
                subgoal by auto
                 apply simp
                by auto
              done
            done
          subgoal
            apply(elim combine_blocks_unpairE2)
               apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of k])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of j])
                subgoal by auto
                 apply simp
                by auto
              done
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of i])
                subgoal by auto
                 apply simp
                by auto
              done
            done
          done
        done
      text \<open>case 3 - 4\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(3)[of k])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(4)[of j])
            subgoal by auto
                 apply simp
            by auto
          done
        done
      text \<open>case 3 - 5\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases"ch2\<in>chs")
        subgoal
          apply(cases"ch1\<in>chs")
          subgoal 
            apply(elim combine_blocks_pairE)
              apply auto
            apply(rule interrupt_sol_cg.intros(2))
             apply auto
            unfolding cond_gassn2_def
            apply auto
            subgoal
              apply(rule com_of_specs22_sync_prop1[of i _ ch2 P j _ Q])
                 apply auto
              unfolding exists_gassn_def
              apply(rule exI[where x= v2])
              apply(rule )
              by auto
            subgoal
              apply(rule disj_gassn_disjI1)+
              apply(rule com_of_specs22_sync_prop1[of i _ ch2 P j _ Q])
                 apply auto
              unfolding exists_gassn_def
              apply(rule exI[where x= v2])
              apply(rule )
              by auto
            subgoal
              apply(rule disj_gassn_disjI1)+
              apply(rule com_of_specs22_sync_prop1[of i _ ch2 P j _ Q])
                 apply auto
              unfolding exists_gassn_def
              apply(rule exI[where x= v2])
              apply(rule )
              by auto
            subgoal
              apply(rule disj_gassn_disjI1)+
              apply(rule com_of_specs22_sync_prop1[of i _ ch2 P j _ Q])
                 apply auto
              unfolding exists_gassn_def
              apply(rule exI[where x= v2])
              apply(rule )
              by auto
            done
          subgoal
            apply(elim combine_blocks_unpairE1)
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of k])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of j])
                subgoal by auto
                 apply simp
                by auto
              done
            done
          done
        subgoal
          apply(cases "ch1\<in>chs")
          subgoal
            apply(elim combine_blocks_unpairE1')
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of i])
                subgoal by auto
                 apply simp
                by auto
              done
            done
          subgoal
            apply(elim combine_blocks_unpairE2)
               apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of k])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of j])
                subgoal by auto
                 apply simp
                by auto
              done
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of i])
                subgoal by auto
                 apply simp
                by auto
              done
            done
          done
        done
      text \<open>case 3 - 6\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(3)[of k])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(6)[of j])
            subgoal by auto
                 apply simp
            by auto
          done
        done
      text \<open>case 4 - 1\<close>
      subgoal for i ch1 P d v1 tr1' a1 b1 p1 tr2' a2 b2 p2
        apply(elim combine_blocks_waitE1)
        using assms by auto
      text \<open>case 4 - 2\<close>
      subgoal for i ch1 P d v tr1' a1 b1 p1
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def
        apply auto
        apply(rule disj_gassn_disjI2)
        apply rule
              apply auto
        apply(rule interrupt_sol_cg.intros(4)[of i])
        subgoal by auto
             apply simp
        by auto
      text \<open>case 4 - 3\<close>
      subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply rule
                      apply auto
                apply(rule interrupt_sol_cg.intros(4)[of i])
                subgoal by auto
                     apply simp
                by auto
              done
            done
      text \<open>case 4 - 4\<close>
      subgoal 
        apply(elim combine_blocks_waitE1)
        using assms by auto
      text \<open>case 4 - 5\<close>
      subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply rule
                      apply auto
                apply(rule interrupt_sol_cg.intros(4)[of i])
                subgoal by auto
                     apply simp
                by auto
              done
            done
      text \<open>case 4 - 6\<close>
      subgoal 
        apply(elim combine_blocks_waitE1)
        using assms by auto
      text \<open>case 5 - 1\<close>
      subgoal for i ch1 P v tr1' tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(5)[of "k"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(1))
            by auto
          done
        done
      text \<open>case 5 - 2\<close>
      subgoal for i ch1 P v tr1'
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def 
        apply auto
        subgoal
          apply(rule disj_gassn_disjI2)
          apply rule
                apply auto
          apply(rule )
          by simp
        subgoal
          apply(rule disj_gassn_disjI2)
          apply(rule disj_gassn_disjI1)
          apply rule
                apply auto
          apply rule
          by simp
        done
      text \<open>case 5 - 3\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases"ch2\<in>chs")
        subgoal
          apply(cases"ch1\<in>chs")
          subgoal 
            apply(elim combine_blocks_pairE)
              apply auto
            apply(rule interrupt_sol_cg.intros(2))
             apply auto
            unfolding cond_gassn2_def
            apply auto
            subgoal
              apply(rule com_of_specs22_sync_prop2[of i _ ch2 P j _ Q])
                 apply auto
              unfolding exists_gassn_def
              apply(rule exI[where x= v2])
              apply(rule )
              by auto
            subgoal
              apply(rule disj_gassn_disjI1)+
              apply(rule com_of_specs22_sync_prop2[of i _ ch2 P j _ Q])
                 apply auto
              unfolding exists_gassn_def
              apply(rule exI[where x= v2])
              apply(rule )
              by auto
            subgoal
              apply(rule disj_gassn_disjI1)+
              apply(rule com_of_specs22_sync_prop2[of i _ ch2 P j _ Q])
                 apply auto
              unfolding exists_gassn_def
              apply(rule exI[where x= v2])
              apply(rule )
              by auto
            subgoal
              apply(rule disj_gassn_disjI1)+
              apply(rule com_of_specs22_sync_prop2[of i _ ch2 P j _ Q])
                 apply auto
              unfolding exists_gassn_def
              apply(rule exI[where x= v2])
              apply(rule )
              by auto
            done
          subgoal
            apply(elim combine_blocks_unpairE1)
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of k])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of j])
                subgoal by auto
                 apply simp
                by auto
              done
            done
          done
        subgoal
          apply(cases "ch1\<in>chs")
          subgoal
            apply(elim combine_blocks_unpairE1')
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of i])
                subgoal by auto
                 apply simp
                by auto
              done
            done
          subgoal
            apply(elim combine_blocks_unpairE2)
               apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of k])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of j])
                subgoal by auto
                 apply simp
                by auto
              done
            subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of i])
                subgoal by auto
                 apply simp
                by auto
              done
            done
          done
        done
      text \<open>case 5 - 4\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(5)[of k])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(4)[of j])
            subgoal by auto
                 apply simp
            by auto
          done
        done
      text \<open>case 5 - 5\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases"ch2\<in>chs")
        subgoal
          apply(cases"ch1\<in>chs")
          subgoal 
            apply(elim combine_blocks_pairE)
              by auto
          subgoal
            apply(elim combine_blocks_unpairE1)
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of k])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of j])
                subgoal by auto
                 apply simp
                by auto
              done
            done
          done
        subgoal
          apply(cases "ch1\<in>chs")
          subgoal
            apply(elim combine_blocks_unpairE1')
              apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of i])
                subgoal by auto
                 apply simp
                by auto
              done
            done
          subgoal
            apply(elim combine_blocks_unpairE2)
               apply auto
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of k])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of j])
                subgoal by auto
                 apply simp
                by auto
              done
            subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply(rule)
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of i])
                subgoal by auto
                 apply simp
                by auto
              done
            done
          done
        done
      text \<open>case 5 - 6\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(5)[of k])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(6)[of j])
            subgoal by auto
                 apply simp
            by auto
          done
        done
      text \<open>case 6 - 1\<close>
      subgoal for i ch1 P d v1 tr1' a1 b1 p1 tr2' a2 b2 p2
        apply(elim combine_blocks_waitE1)
        using assms by auto
      text \<open>case 6 - 2\<close>
      subgoal for i ch1 P d v tr1' a1 b1 p1
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def
        apply auto
        apply(rule disj_gassn_disjI2)
        apply rule
              apply auto
        apply(rule interrupt_sol_cg.intros(6)[of i])
        subgoal by auto
             apply simp
        by auto
      text \<open>case 6 - 3\<close>
      subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply rule
                      apply auto
                apply(rule interrupt_sol_cg.intros(6)[of i])
                subgoal by auto
                     apply simp
                by auto
              done
            done
      text \<open>case 6 - 4\<close>
      subgoal 
        apply(elim combine_blocks_waitE1)
        using assms by auto
      text \<open>case 6 - 5\<close>
      subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
              apply auto
              subgoal for k
                apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
                subgoal by auto
                 apply simp
                apply rule
                      apply auto
                apply(rule interrupt_sol_cg.intros(6)[of i])
                subgoal by auto
                     apply simp
                by auto
              done
            done
      text \<open>case 6 - 6\<close>
      subgoal 
        apply(elim combine_blocks_waitE1)
        using assms by auto
      done
    done
  done

thm sync_gassn_interrupt_sol_interrupt_sol1

lemma sync_gassn_interrupt_sol_interrupt_solInf1:
  assumes "compat_rdy (rdy_of_comm_specg2 specs1) (rdy_of_comm_specg2 specs2)" 
     and  "pn1 \<in> pns1"
shows
  "sync_gassn chs pns1 pns2 (interrupt_sol_cg I1 pn1 e1 G1 specs1) (interrupt_solInf_cg I2 specs2) s0 \<Longrightarrow>\<^sub>G
   interrupt_sol_cg (merge_inv I1 I2) pn1 e1 
      (\<lambda> d. sync_gassn chs pns1 pns2 (G1 d) (interrupt_solInf_cg (delay_inv d I2) (map (spec_wait_of d) specs2)))
         ((map (ii1 chs pns1 pns2 I2 specs2) (comm_specg2_notin_chs specs1 chs))@  
          (map (if2 chs pns1 pns2 I1 pn1 e1 G1 specs1) (comm_specg2_notin_chs specs2 chs))) s0"
unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply(subgoal_tac"e1 (the (s0 pn1)) = e1 (the (s11 pn1))")
       prefer 2
      subgoal 
        apply auto
        apply(subst merge_state_eval1[of pn1]) using assms by auto
      apply (elim interrupt_sol_cg.cases) apply auto
           apply (auto elim!: interrupt_solInf_cg.cases)[6]
      text \<open>case 1 - 1\<close>
      subgoal for tr1' a1 b1 p1 j ch2 Q v tr2'
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(1))
            subgoal by auto
               apply simp
            by auto
          done
        done
      text \<open>case 1 - 2\<close>
      subgoal for tr1' a1 b1 p1 j ch2 Q d v tr2' a2 b2 p2
        apply(cases "d>e1 (the (s11 pn1))")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply(auto simp add:assms)
          subgoal for tr'
            apply(rule interrupt_sol_cg.intros(1))
                apply auto
            subgoal 
              apply rule
                    apply simp
              apply auto
              apply(rule interrupt_solInf_cg.intros(2)[of j])
              subgoal by auto
                  apply simp
                 apply auto
              apply rule
              by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        apply(cases "d=e1 (the (s11 pn1))")
        subgoal
          apply(elim combine_blocks_waitE2')
             apply(auto simp add:assms)
          subgoal for tr'
            apply(rule interrupt_sol_cg.intros(1))
                apply auto
            subgoal 
              apply rule
                    apply simp
              apply auto
              apply(rule interrupt_solInf_cg.intros(1)[of j])
              subgoal by auto
                  apply simp
              by auto
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        apply(cases "d<e1 (the (s11 pn1))")
        subgoal
          apply(elim combine_blocks_waitE4)
             apply(auto simp add:assms)
          apply(cases "ch2\<in>chs")
          subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(4)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
                 apply simp
                apply auto
            subgoal
              apply rule
                  apply auto
              apply(rule interrupt_sol_cg.intros(1))
              subgoal by auto
               apply simp
                apply auto
              apply rule
              by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        done
      by auto
    text \<open>case 1 - 3\<close>
      subgoal for tr1' a1 b1 p1 j ch2 Q v tr2'
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(1))
            subgoal by auto
               apply simp
            by auto
          done
        done
      text \<open>case 1 - 4\<close>
      subgoal for tr1' a1 b1 p1 j ch2 Q d v tr2' a2 b2 p2
        apply(cases "d>e1 (the (s11 pn1))")
        subgoal
          apply(elim combine_blocks_waitE3)
             apply(auto simp add:assms)
          subgoal for tr'
            apply(rule interrupt_sol_cg.intros(1))
                apply auto
            subgoal 
              apply rule
                    apply simp
              apply auto
              apply(rule interrupt_solInf_cg.intros(4)[of j])
              subgoal by auto
                  apply simp
                 apply auto
              apply rule
              by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        apply(cases "d=e1 (the (s11 pn1))")
        subgoal
          apply(elim combine_blocks_waitE2')
             apply(auto simp add:assms)
          subgoal for tr'
            apply(rule interrupt_sol_cg.intros(1))
                apply auto
            subgoal 
              apply rule
                    apply simp
              apply auto
              apply(rule interrupt_solInf_cg.intros(3)[of j])
              subgoal by auto
                  apply simp
              by auto
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        apply(cases "d<e1 (the (s11 pn1))")
        subgoal
          apply(elim combine_blocks_waitE4)
             apply(auto simp add:assms)
          apply(cases "ch2\<in>chs")
          subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(6)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
                 apply simp
                apply auto
            subgoal
              apply rule
                  apply auto
              apply(rule interrupt_sol_cg.intros(1))
              subgoal by auto
               apply simp
                apply auto
              apply rule
              by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        done
      by auto
    text \<open>case 2 - 1\<close>
    subgoal for j ch2 Q v tr2'
      apply(rule interrupt_sol_cg.intros(2))
       apply auto
      apply rule
            apply auto
      apply(rule interrupt_solInf_cg.intros(1)[of j])
      subgoal by auto
       apply simp
      by auto
    text \<open>case 2 - 2\<close>
    subgoal for j ch2 Q d v tr2' a b p
      apply(rule interrupt_sol_cg.intros(2))
       apply auto
      apply rule
            apply auto
      apply(rule interrupt_solInf_cg.intros(2)[of j])
      subgoal by auto
       apply simp
      by auto
    text \<open>case 2 - 3\<close>
    subgoal for j
      apply(rule interrupt_sol_cg.intros(2))
       apply auto
      apply rule
            apply auto
      apply(rule interrupt_solInf_cg.intros(3)[of j])
      subgoal by auto
       apply simp
      by auto
    text \<open>case 2 - 4\<close>
    subgoal for j
      apply(rule interrupt_sol_cg.intros(2))
       apply auto
      apply rule
            apply auto
      apply(rule interrupt_solInf_cg.intros(4)[of j])
      subgoal by auto
       apply simp
      by auto
    text \<open>case 3 - 1\<close>
    subgoal for i ch1 P v1 tr1' j ch2 Q v2' tr2'
      apply(cases "ch2\<in>chs")
      subgoal 
        apply(cases "ch1\<in>chs")
        subgoal 
          apply(elim combine_blocks_pairE)
          by auto               
        subgoal
          apply(elim combine_blocks_unpairE1)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(3)[of "k"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_solInf_cg.intros(1)[of j])
            subgoal by auto
             apply simp
            by auto
          done
        done
      done
      subgoal 
        apply(cases "ch1\<in>chs")
         apply(elim combine_blocks_unpairE1')
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(3)[of i])
            subgoal by auto
             apply simp
            by auto
          done
        subgoal
          apply(elim combine_blocks_unpairE2)
          apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(1)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(3)[of i])
              subgoal by auto
               apply simp
              by auto
            done
          done
        done
      done
    text \<open>case 3 - 2\<close>
    subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a2 b2 p2
      apply(cases "ch1\<in>chs")
      subgoal by(elim combine_blocks_pairE2)
      apply(elim combine_blocks_unpairE3)
       apply auto
      subgoal for tr'
        using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
        apply auto
        subgoal for k
          apply(rule interrupt_sol_cg.intros(3)[of k])
          subgoal by auto
           apply simp
          apply rule
                apply auto
          apply(rule interrupt_solInf_cg.intros(2)[of j])
          subgoal by auto
              apply simp
          by auto
        done
      done
    text \<open>case 3 - 3\<close>
    subgoal for i ch1 P v1 tr1' j ch2 Q v2' tr2'
      apply(cases "ch2\<in>chs")
      subgoal 
        apply(cases "ch1\<in>chs")
        subgoal 
          apply(elim combine_blocks_pairE)
            apply auto
          using rdy_of_comm_specg2_prop1[of i specs1 ch1 P]
          using rdy_of_comm_specg2_prop2[of j specs2 ch2 Q]
          using assms
          apply auto
          by (smt (verit, ccfv_SIG) compat_rdy.elims(2) disjoint_iff fst_conv snd_conv)             
        subgoal
          apply(elim combine_blocks_unpairE1)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(3)[of "k"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_solInf_cg.intros(3)[of j])
            subgoal by auto
             apply simp
            by auto
          done
        done
      done
      subgoal 
        apply(cases "ch1\<in>chs")
         apply(elim combine_blocks_unpairE1')
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(3)[of i])
            subgoal by auto
             apply simp
            by auto
          done
        subgoal
          apply(elim combine_blocks_unpairE2)
          apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(3)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(3)[of i])
              subgoal by auto
               apply simp
              by auto
            done
          done
        done
      done
    text \<open>case 3 - 4\<close>
    subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a2 b2 p2
      apply(cases "ch1\<in>chs")
      subgoal by(elim combine_blocks_pairE2)
      apply(elim combine_blocks_unpairE3)
       apply auto
      subgoal for tr'
        using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
        apply auto
        subgoal for k
          apply(rule interrupt_sol_cg.intros(3)[of k])
          subgoal by auto
           apply simp
          apply rule
                apply auto
          apply(rule interrupt_solInf_cg.intros(4)[of j])
          subgoal by auto
              apply simp
          by auto
        done
      done
    text \<open>case 4 - 1\<close>
    subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
      apply(cases "ch2\<in>chs")
      subgoal by(elim combine_blocks_pairE2')
      apply(elim combine_blocks_unpairE3')
       apply auto
      subgoal for tr'
        using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
        apply auto
        subgoal for k
          apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
          subgoal by auto
           apply simp
          apply rule
                apply auto
          apply(rule interrupt_sol_cg.intros(4)[of i])
          subgoal by auto
              apply simp
          by auto
        done
      done
    text \<open>case 4 - 2\<close>
    subgoal for i ch1 P d1 v1 tr1' a1 b1 p1 j ch2 Q d2 v2 tr2' a2 b2 p2
      apply(cases "d1<d2")
      subgoal
        apply(elim combine_blocks_waitE3)
           apply (auto simp add:assms)
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(4)[of k])
            subgoal by auto
                 apply simp
                apply auto
            subgoal
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(2)[of j])
              subgoal by auto
                  apply simp
                 apply auto
              apply rule
              by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        done
      apply(cases "d1>d2")
      subgoal
        apply(elim combine_blocks_waitE4)
           apply (auto simp add:assms)
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(4)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
                 apply simp
                apply auto
            subgoal
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(4)[of i])
              subgoal by auto
                  apply simp
                 apply auto
              apply rule
              by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        done
      apply(cases "d1=d2")
      subgoal
        apply(elim combine_blocks_waitE2')
           apply (auto simp add:assms)
        apply(cases "ch2\<in>chs")
         apply(cases "ch1\<in>chs")
        subgoal apply(elim combine_blocks_pairE) by auto
        subgoal 
          apply(elim combine_blocks_unpairE1)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(4)[of "k"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_solInf_cg.intros(1)[of j])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          done
        apply(cases "ch1\<in>chs")
        subgoal 
          apply(elim combine_blocks_unpairE1')
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(4)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of i])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          done
        subgoal
          apply(elim combine_blocks_unpairE2)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(4)[of "k"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_solInf_cg.intros(1)[of j])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(4)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of i])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          done
        done
      by auto
    text \<open>case 4 - 3\<close>
    subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
      apply(cases "ch2\<in>chs")
      subgoal by(elim combine_blocks_pairE2')
      apply(elim combine_blocks_unpairE3')
       apply auto
      subgoal for tr'
        using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
        apply auto
        subgoal for k
          apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
          subgoal by auto
           apply simp
          apply rule
                apply auto
          apply(rule interrupt_sol_cg.intros(4)[of i])
          subgoal by auto
              apply simp
          by auto
        done
      done
    text \<open>case 4 - 4\<close>
    subgoal for i ch1 P d1 v1 tr1' a1 b1 p1 j ch2 Q d2 v2 tr2' a2 b2 p2
      apply(cases "d1<d2")
      subgoal
        apply(elim combine_blocks_waitE3)
           apply (auto simp add:assms)
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(4)[of k])
            subgoal by auto
                 apply simp
                apply auto
            subgoal
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(4)[of j])
              subgoal by auto
                  apply simp
                 apply auto
              apply rule
              by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        done
      apply(cases "d1>d2")
      subgoal
        apply(elim combine_blocks_waitE4)
           apply (auto simp add:assms)
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(6)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
                 apply simp
                apply auto
            subgoal
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(4)[of i])
              subgoal by auto
                  apply simp
                 apply auto
              apply rule
              by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        done
      apply(cases "d1=d2")
      subgoal
        apply(elim combine_blocks_waitE2')
           apply (auto simp add:assms)
        apply(cases "ch2\<in>chs")
         apply(cases "ch1\<in>chs")
        subgoal apply(elim combine_blocks_pairE) 
          using rdy_of_comm_specg2_prop1[of i specs1 ch1 P]
          using rdy_of_comm_specg2_prop2[of j specs2 ch2 Q]
          using assms
          apply auto
          by (smt (verit, ccfv_SIG) compat_rdy.elims(2) disjoint_iff fst_conv snd_conv)
        subgoal 
          apply(elim combine_blocks_unpairE1)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(4)[of "k"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_solInf_cg.intros(3)[of j])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          done
        apply(cases "ch1\<in>chs")
        subgoal 
          apply(elim combine_blocks_unpairE1')
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(6)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of i])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          done
        subgoal
          apply(elim combine_blocks_unpairE2)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(4)[of "k"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_solInf_cg.intros(3)[of j])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(6)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_sol_cg.intros(3)[of i])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          done
        done
      by auto
    text \<open>case 5 - 1\<close>
    subgoal for i ch1 P v1 tr1' j ch2 Q v2' tr2'
      apply(cases "ch2\<in>chs")
      subgoal 
        apply(cases "ch1\<in>chs")
        subgoal 
          apply(elim combine_blocks_pairE)
          using rdy_of_comm_specg2_prop2[of i specs1 ch1 P]
          using rdy_of_comm_specg2_prop1[of j specs2 ch2 Q]
          using assms
          apply auto
          by (smt (verit, ccfv_SIG) compat_rdy.elims(2) disjoint_iff fst_conv snd_conv)              
        subgoal
          apply(elim combine_blocks_unpairE1)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(5)[of "k"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_solInf_cg.intros(1)[of j])
            subgoal by auto
             apply simp
            by auto
          done
        done
      done
      subgoal 
        apply(cases "ch1\<in>chs")
         apply(elim combine_blocks_unpairE1')
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(5)[of i])
            subgoal by auto
             apply simp
            by auto
          done
        subgoal
          apply(elim combine_blocks_unpairE2)
          apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(1)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          subgoal for tr'
              using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(5)[of i])
              subgoal by auto
               apply simp
              by auto
            done
          done
        done
      done
    text \<open>case 5 - 2\<close>
    subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a2 b2 p2
      apply(cases "ch1\<in>chs")
      subgoal by(elim combine_blocks_pairE2)
      apply(elim combine_blocks_unpairE3)
       apply auto
      subgoal for tr'
        using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
        apply auto
        subgoal for k
          apply(rule interrupt_sol_cg.intros(5)[of k])
          subgoal by auto
           apply simp
          apply rule
                apply auto
          apply(rule interrupt_solInf_cg.intros(2)[of j])
          subgoal by auto
              apply simp
          by auto
        done
      done
    text \<open>case 5 - 3\<close>
    subgoal for i ch1 P v1 tr1' j ch2 Q v2' tr2'
      apply(cases "ch2\<in>chs")
      subgoal 
        apply(cases "ch1\<in>chs")
        subgoal 
          apply(elim combine_blocks_pairE)
            by auto                       
        subgoal
          apply(elim combine_blocks_unpairE1)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(5)[of "k"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_solInf_cg.intros(3)[of j])
            subgoal by auto
             apply simp
            by auto
          done
        done
      done
      subgoal 
        apply(cases "ch1\<in>chs")
         apply(elim combine_blocks_unpairE1')
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(5)[of i])
            subgoal by auto
             apply simp
            by auto
          done
        subgoal
          apply(elim combine_blocks_unpairE2)
          apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(3)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          subgoal for tr'
              using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(5)[of i])
              subgoal by auto
               apply simp
              by auto
            done
          done
        done
      done
    text \<open>case 5 - 4\<close>
    subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a2 b2 p2
      apply(cases "ch1\<in>chs")
      subgoal by(elim combine_blocks_pairE2)
      apply(elim combine_blocks_unpairE3)
       apply auto
      subgoal for tr'
        using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
        apply auto
        subgoal for k
          apply(rule interrupt_sol_cg.intros(5)[of k])
          subgoal by auto
           apply simp
          apply rule
                apply auto
          apply(rule interrupt_solInf_cg.intros(4)[of j])
          subgoal by auto
              apply simp
          by auto
        done
      done
    text \<open>case 6 - 1\<close>
    subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
      apply(cases "ch2\<in>chs")
      subgoal by(elim combine_blocks_pairE2')
      apply(elim combine_blocks_unpairE3')
       apply auto
      subgoal for tr'
        using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
        apply auto
        subgoal for k
          apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
          subgoal by auto
           apply simp
          apply rule
                apply auto
          apply(rule interrupt_sol_cg.intros(6)[of i])
          subgoal by auto
              apply simp
          by auto
        done
      done
    text \<open>case 6 - 2\<close>
    subgoal for i ch1 P d1 v1 tr1' a1 b1 p1 j ch2 Q d2 v2 tr2' a2 b2 p2
      apply(cases "d1<d2")
      subgoal
        apply(elim combine_blocks_waitE3)
           apply (auto simp add:assms)
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(6)[of k])
            subgoal by auto
                 apply simp
                apply auto
            subgoal
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(2)[of j])
              subgoal by auto
                  apply simp
                 apply auto
              apply rule
              by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        done
      apply(cases "d1>d2")
      subgoal
        apply(elim combine_blocks_waitE4)
           apply (auto simp add:assms)
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(4)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
                 apply simp
                apply auto
            subgoal
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(6)[of i])
              subgoal by auto
                  apply simp
                 apply auto
              apply rule
              by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        done
      apply(cases "d1=d2")
      subgoal
        apply(elim combine_blocks_waitE2')
           apply (auto simp add:assms)
        apply(cases "ch2\<in>chs")
         apply(cases "ch1\<in>chs")
        subgoal 
          apply(elim combine_blocks_pairE) 
          using rdy_of_comm_specg2_prop2[of i specs1 ch1 P]
          using rdy_of_comm_specg2_prop1[of j specs2 ch2 Q]
          using assms
          apply auto
          by (smt (verit, ccfv_SIG) compat_rdy.elims(2) disjoint_iff fst_conv snd_conv)
        subgoal 
          apply(elim combine_blocks_unpairE1)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(6)[of "k"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_solInf_cg.intros(1)[of j])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          done
        apply(cases "ch1\<in>chs")
        subgoal 
          apply(elim combine_blocks_unpairE1')
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(4)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of i])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          done
        subgoal
          apply(elim combine_blocks_unpairE2)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(6)[of "k"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_solInf_cg.intros(1)[of j])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(4)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of i])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          done
        done
      by auto
    text \<open>case 4 - 3\<close>
    subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
      apply(cases "ch2\<in>chs")
      subgoal by(elim combine_blocks_pairE2')
      apply(elim combine_blocks_unpairE3')
       apply auto
      subgoal for tr'
        using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
        apply auto
        subgoal for k
          apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
          subgoal by auto
           apply simp
          apply rule
                apply auto
          apply(rule interrupt_sol_cg.intros(6)[of i])
          subgoal by auto
              apply simp
          by auto
        done
      done
    text \<open>case 4 - 4\<close>
    subgoal for i ch1 P d1 v1 tr1' a1 b1 p1 j ch2 Q d2 v2 tr2' a2 b2 p2
      apply(cases "d1<d2")
      subgoal
        apply(elim combine_blocks_waitE3)
           apply (auto simp add:assms)
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(6)[of k])
            subgoal by auto
                 apply simp
                apply auto
            subgoal
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(4)[of j])
              subgoal by auto
                  apply simp
                 apply auto
              apply rule
              by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        done
      apply(cases "d1>d2")
      subgoal
        apply(elim combine_blocks_waitE4)
           apply (auto simp add:assms)
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(6)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
                 apply simp
                apply auto
            subgoal
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(6)[of i])
              subgoal by auto
                  apply simp
                 apply auto
              apply rule
              by (meson add_increasing2 atLeastAtMost_iff le_diff_eq nless_le)
            apply(rule merge_rdy_of_comm_specg2_prop''')
            apply(rule merge_inv.intros)
            by auto
          done
        done
      apply(cases "d1=d2")
      subgoal
        apply(elim combine_blocks_waitE2')
           apply (auto simp add:assms)
        apply(cases "ch2\<in>chs")
         apply(cases "ch1\<in>chs")
        subgoal apply(elim combine_blocks_pairE) 
          by auto
        subgoal 
          apply(elim combine_blocks_unpairE1)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(6)[of "k"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_solInf_cg.intros(3)[of j])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          done
        apply(cases "ch1\<in>chs")
        subgoal 
          apply(elim combine_blocks_unpairE1')
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(6)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of i])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          done
        subgoal
          apply(elim combine_blocks_unpairE2)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(6)[of "k"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_solInf_cg.intros(3)[of j])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(6)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
                   apply simp
                  apply auto
              subgoal
                apply rule
                      apply auto
                apply(rule interrupt_sol_cg.intros(5)[of i])
                subgoal by auto
                    apply simp
                   by auto
              apply(rule merge_rdy_of_comm_specg2_prop''')
              apply(rule merge_inv.intros)
              by auto
            done
          done
        done
      by auto
    done
  done
  done


thm sync_gassn_interrupt_sol_interrupt_sol2
thm sync_gassn_interrupt_sol_interrupt_solInf1
thm sync_gassn_interrupt_solInf_interrupt_solInf1

lemma sync_gassn_interrupt_sol_interrupt_solInf2:
  assumes "\<not>compat_rdy (rdy_of_comm_specg2 specs1) (rdy_of_comm_specg2 specs2)" 
     and  "pn1 \<in> pns1"
shows
  "sync_gassn chs pns1 pns2 (interrupt_sol_cg I1 pn1 e1 G1 specs1) (interrupt_solInf_cg I2 specs2) s0 \<Longrightarrow>\<^sub>G
   interrupt_sol_cg (merge_inv I1 I2) pp (\<lambda>_ .0) 
         (\<lambda>_ . IFG  (\<lambda>s0. e1 (the (s0 pn1)) > 0) 
               THEN com_of_specs22_sync chs pns1 pns2 (com_of_specs2 chs specs1 specs2)
               ELSE (com_of_specs22_sync chs pns1 pns2 (com_of_specs2 chs specs1 specs2) 
                            \<or>\<^sub>g sync_gassn chs pns1 pns2 (G1 0) (interrupt_solInf_cg I2 specs2))
               FI)
          ((map (ii1 chs pns1 pns2 I2 specs2) (comm_specg2_notin_chs specs1 chs))@  
           (map (if2 chs pns1 pns2 I1 pn1 e1 G1 specs1) (comm_specg2_notin_chs specs2 chs))) s0"
unfolding entails_g_def apply auto
  subgoal for s tr
    apply (elim sync_gassn.cases) apply auto
    subgoal for s11 s12 s21 s22 tr1 tr2
      apply(subgoal_tac"e1 (the (s0 pn1)) = e1 (the (s11 pn1))")
       prefer 2
      subgoal 
        apply auto
        apply(subst merge_state_eval1[of pn1]) using assms by auto
        apply (elim interrupt_sol_cg.cases) apply auto
           apply (auto elim!: interrupt_solInf_cg.cases)[6]
      text \<open>case 1 - 1\<close> 
      subgoal for tr1' a1 b1 p1 j ch2 Q v tr2'
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(1))
            by auto
          done
        done
      text \<open>case 1 - 2\<close>
      subgoal for tr1' a1 b1 p1 j ch2 Q d v tr2' a2 b2 p2
        apply(elim combine_blocks_waitE1)
        by(auto simp add:assms)
      text \<open>case 1 - 3\<close> 
      subgoal for tr1' a1 b1 p1 j ch2 Q v tr2'
        apply(cases "ch2\<in>chs")
        subgoal by(elim combine_blocks_pairE2')
        apply(elim combine_blocks_unpairE3')
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
          apply auto
          subgoal for k
            apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
            subgoal by auto
             apply simp
            apply rule
                  apply auto
            apply(rule interrupt_sol_cg.intros(1))
            by auto
          done
        done
      text \<open>case 1 - 4\<close>
      subgoal for tr1' a1 b1 p1 j ch2 Q d v tr2' a2 b2 p2
        apply(elim combine_blocks_waitE1)
        by(auto simp add:assms) 
      text \<open>case 2 - 1\<close>
      subgoal for j ch2 Q v tr2'
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def 
        apply auto
        apply (rule disj_gassn_disjI2)
        apply rule
              apply auto
        apply(rule interrupt_solInf_cg.intros(1)[of j])
        subgoal by auto
         apply simp
        by auto
      text \<open>case 2 - 2\<close>
      subgoal for j ch2 Q d v tr2' a2 b2 p2
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def 
        apply auto
        apply (rule disj_gassn_disjI2)
        apply rule
              apply auto
        apply(rule interrupt_solInf_cg.intros(2)[of j])
        subgoal by auto
         apply simp
        by auto
      text \<open>case 2 - 3\<close>
      subgoal for j ch2 Q v tr2'
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def 
        apply auto
        apply (rule disj_gassn_disjI2)
        apply rule
              apply auto
        apply(rule interrupt_solInf_cg.intros(3)[of j])
        subgoal by auto
         apply simp
        by auto
      text \<open>case 2 - 4\<close>
      subgoal for j ch2 Q d v tr2' a2 b2 p2
        apply(rule interrupt_sol_cg.intros(2))
         apply auto
        unfolding cond_gassn2_def 
        apply auto
        apply (rule disj_gassn_disjI2)
        apply rule
              apply auto
        apply(rule interrupt_solInf_cg.intros(4)[of j])
        subgoal by auto
         apply simp
        by auto
      text \<open>case 3 - 1\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
         apply(cases "ch1\<in>chs")
        subgoal
          apply(elim combine_blocks_pairE)
          by auto
        subgoal
          apply(elim combine_blocks_unpairE1)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(1)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          done
        apply(cases "ch1\<in>chs")
        subgoal
          apply(elim combine_blocks_unpairE1')
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(3)[of i])
              subgoal by auto
               apply simp
              by auto
            done
          done
        subgoal
          apply(elim combine_blocks_unpairE2)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(1)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(3)[of i])
              subgoal by auto
               apply simp
              by auto
            done
          done
        done
      text \<open>case 3 - 2\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(2)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          done
      text \<open>case 3 - 3\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
         apply(cases "ch1\<in>chs")
        subgoal
          apply(elim combine_blocks_pairE)
            apply auto
          apply(rule interrupt_sol_cg.intros(2))
           apply auto
          unfolding cond_gassn2_def
          apply auto
          subgoal
            apply(rule com_of_specs22_sync_prop1[of i _ ch2 P j _ Q])
               apply auto
            unfolding exists_gassn_def
            apply(rule exI[where x= v2])
            apply(rule )
            by auto
          subgoal
            apply(rule disj_gassn_disjI1)
            apply(rule com_of_specs22_sync_prop1[of i _ ch2 P j _ Q])
               apply auto
            unfolding exists_gassn_def
            apply(rule exI[where x= v2])
            apply(rule )
            by auto
          done
        subgoal
          apply(elim combine_blocks_unpairE1)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(3)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          done
        apply(cases "ch1\<in>chs")
        subgoal
          apply(elim combine_blocks_unpairE1')
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(3)[of i])
              subgoal by auto
               apply simp
              by auto
            done
          done
        subgoal
          apply(elim combine_blocks_unpairE2)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(3)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(3)[of i])
              subgoal by auto
               apply simp
              by auto
            done
          done
        done
      text \<open>case 3 - 4\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop1[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(4)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          done
        text \<open>case 4 - 1\<close>
        subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
          apply(cases "ch2\<in>chs")
          subgoal by(elim combine_blocks_pairE2')
          apply(elim combine_blocks_unpairE3')
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(4)[of i])
              subgoal by auto
                   apply simp
              by auto
            done
          done
        text \<open>case 4 - 2\<close>
        subgoal
          apply(elim combine_blocks_waitE1)
          by(auto simp add:assms)
        text \<open>case 4 - 3\<close>
        subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
          apply(cases "ch2\<in>chs")
          subgoal by(elim combine_blocks_pairE2')
          apply(elim combine_blocks_unpairE3')
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(4)[of i])
              subgoal by auto
                   apply simp
              by auto
            done
          done
      text \<open>case 4 - 4\<close>
      subgoal
        apply(elim combine_blocks_waitE1)
        by(auto simp add:assms)
      text \<open>case 5 - 1\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
         apply(cases "ch1\<in>chs")
        subgoal
          apply(elim combine_blocks_pairE)
          apply auto
          apply(rule interrupt_sol_cg.intros(2))
           apply auto
          unfolding cond_gassn2_def
          apply auto
          subgoal
            apply(rule com_of_specs22_sync_prop2[of i _ ch2 P j _ Q])
               apply auto
            unfolding exists_gassn_def
            apply(rule exI[where x= v2])
            apply(rule )
            by auto
          subgoal
            apply(rule disj_gassn_disjI1)
            apply(rule com_of_specs22_sync_prop2[of i _ ch2 P j _ Q])
               apply auto
            unfolding exists_gassn_def
            apply(rule exI[where x= v2])
            apply(rule )
            by auto
          done
        subgoal
          apply(elim combine_blocks_unpairE1)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(1)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          done
        apply(cases "ch1\<in>chs")
        subgoal
          apply(elim combine_blocks_unpairE1')
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(5)[of i])
              subgoal by auto
               apply simp
              by auto
            done
          done
        subgoal
          apply(elim combine_blocks_unpairE2)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(1)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(5)[of i])
              subgoal by auto
               apply simp
              by auto
            done
          done
        done
      text \<open>case 5 - 2\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(2)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          done
      text \<open>case 5 - 3\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q v2 tr2'
        apply(cases "ch2\<in>chs")
         apply(cases "ch1\<in>chs")
        subgoal
          apply(elim combine_blocks_pairE)
          by auto
        subgoal
          apply(elim combine_blocks_unpairE1)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(3)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          done
        apply(cases "ch1\<in>chs")
        subgoal
          apply(elim combine_blocks_unpairE1')
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(5)[of i])
              subgoal by auto
               apply simp
              by auto
            done
          done
        subgoal
          apply(elim combine_blocks_unpairE2)
            apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(3)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(5)[of i])
              subgoal by auto
               apply simp
              by auto
            done
          done
        done
      text \<open>case 5 - 4\<close>
      subgoal for i ch1 P v1 tr1' j ch2 Q d v2 tr2' a2 b2 p2
        apply(cases "ch1\<in>chs")
        subgoal by(elim combine_blocks_pairE2)
        apply(elim combine_blocks_unpairE3)
         apply auto
        subgoal for tr'
          using comm_specg2_notin_chs_prop2[of i specs1 ch1 P chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_solInf_cg.intros(4)[of j])
              subgoal by auto
               apply simp
              by auto
            done
          done
        text \<open>case 6 - 1\<close>
        subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
          apply(cases "ch2\<in>chs")
          subgoal by(elim combine_blocks_pairE2')
          apply(elim combine_blocks_unpairE3')
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop1[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(3)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(6)[of i])
              subgoal by auto
                   apply simp
              by auto
            done
          done
        text \<open>case 6 - 2\<close>
        subgoal
          apply(elim combine_blocks_waitE1)
          by(auto simp add:assms)
        text \<open>case 6 - 3\<close>
        subgoal for i ch1 P d v1 tr1' a1 b1 p1 j ch2 Q v2 tr2'
          apply(cases "ch2\<in>chs")
          subgoal by(elim combine_blocks_pairE2')
          apply(elim combine_blocks_unpairE3')
           apply auto
          subgoal for tr'
            using comm_specg2_notin_chs_prop2[of j specs2 ch2 Q chs]
            apply auto
            subgoal for k
              apply(rule interrupt_sol_cg.intros(5)[of "k+length(comm_specg2_notin_chs specs1 chs)"])
              subgoal by auto
               apply simp
              apply rule
                    apply auto
              apply(rule interrupt_sol_cg.intros(6)[of i])
              subgoal by auto
                   apply simp
              by auto
            done
          done
      text \<open>case 6 - 4\<close>
      subgoal
        apply(elim combine_blocks_waitE1)
        by(auto simp add:assms)
      done
    done
  done

end