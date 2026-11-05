import YM.RG08.Crown.Match
import YM.Extra.WEAK_SCALING_ACTLAW.Color

/-!
# Canonical top kinetic and top interactions r≥3 (=even ranks≥4 once
under powers g^n). -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Crown
open Carrel Camera Room Cloud Glyph Function Finset Filter Lattice Rudder Forms Pert.Bulk
open Wilson WilsonStartup Design Exterior Anchor Rudder.Symmetry RG Loop
open scoped ContDiff Topology PowerSeries BigOperators Classical RealInnerProductSpace
variable {G:YM.Gauge}{P:Side}{k:ℕ}

lemma protectedR (t:Tape k (Market (Tone G.ColorIndex)))(v:Fin k):
    prize G k t=if ∀ i:Fin k,(t i).1=(t v).1∧(t i).2.1=(t v).2.1 then if ((t v).2.1).card=2 then pixel G k (fun i=>(t i).2.2) else 0 else 0:=by
 unfold prize Anchor.extend
 by_cases h:permitted Cover G.ColorIndex 2 t
 · rw [dif_pos h,grown,tsum_eq_single ((t v).1) (by
     intro b hb;unfold sheetCard opening;rw [if_neg (by
       rintro ⟨r,hr⟩;have he:=congrArg (fun g=> (g v).1) hr
       change (t v).1+-b=0 at he;apply hb;exact (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using he)).symm)])]
   unfold sheetCard opening
   have ht (i):((t i).2.1).card=2:=h i
   rw [if_pos (ht v)]
   split_ifs with he hg hg; · rfl
   · exfalso;apply hg; obtain ⟨b,hb⟩:=he;intro i
     have hh:=congrFun hb i;have hy:=congrFun hb v
     have hx:(t i).1+ -(t v).1=0:=congrArg (fun g=> (g i).1) hb
     exact ⟨sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hx),congrArg (fun (y:Cover×TypeFace 2)=> y.2.val) (hh.trans hy.symm)⟩
   · exfalso;apply he; refine ⟨⟨(t v).2.1,h v⟩,funext fun i=>?_⟩;apply Prod.ext
     · change (t i).1+ -(t v).1=0;rw [(hg i).1,add_neg_cancel]
     exact Subtype.ext (hg i).2
   rfl
 rw [dif_neg h];split_ifs with hi hd
 · exfalso;apply h;intro i; rw [(hi i).2];exact hd
 all_goals rfl

lemma home(K:ℕ)(e:Even K)(i:Fin K): Cloak (dressed G K) 2 (prize G K):=by
 refine ⟨Anchor.expand_path (grown_y _),Anchor.expand_grade,?_,?_,?_⟩
 · intro b;funext x;change prize G K (x ∘ b)=_;rw [protectedR (v:=b.symm i),protectedR (v:=i)];simp only [comp_apply,b.apply_symm_apply]
   by_cases h: ∀ j:Fin K,(x j).1=(x i).1∧(x j).2.1=(x i).2.1
   · rw [if_pos h,if_pos (fun j=>h _)]
     split_ifs
     · unfold pixel; exact Tensor.coeff_symm ((inK_diff (G:=G)).of_le le_top) (fun i=>EuclideanSpace.basisFun G.ColorIndex ℝ ((x i).2.2)) b
     rfl
   rw [if_neg h,if_neg (by intro hb;apply h;intro j; obtain ⟨j,rfl⟩:=b.surjective j;exact hb _)]
 · intro b;funext x;rw [orbit_apply,protectedR _ i,protectedR _ i]; unfold Rudder.Symmetry.levy
   -- induced injection on location+type, unused color
   let p(x:Market (Tone G.ColorIndex)):Market (Tone Unit):=(x.1,x.2.1,())
   have hh (x:Market (Tone G.ColorIndex)):p (markCell b x)=markCell b (p x):=rfl
   have hp (a c:Market (Tone G.ColorIndex)):p a=p c↔(a.1=c.1 ∧ a.2.1=c.2.1):=by simp [p]
   have hr (j:Fin K) : ((markTape b x j).1=(markTape b x i).1∧(markTape b x j).2.1=(markTape b x i).2.1)↔(x j).1=(x i).1∧(x j).2.1=(x i).2.1:=by
      change ((markCell b (x j)).1=(markCell b (x i)).1∧(markCell b (x j)).2.1=(markCell b (x i)).2.1)↔_
      rw [←hp,hh,hh,←hp];exact (markEquiv b).injective.eq_iff
   simp_rw [propext (hr _), show (markTape b x i).2.1.card=(x i).2.1.card from marked_card ..]; split_ifs with ht _
   · simp_rw [(ht _).2,Finset.prod_const, Finset.card_univ, Fintype.card_fin]; rw [←e.pow_abs,Rudder.Symmetry.toll_normal,one_pow,one_mul];rfl
   all_goals simp
 intro x
 have hx:=protectedR (G:=G) (v:=i)
 rw [show hat (prize G K) x=(if ∀ j,x j=x i then if (x i).2.card=2 then pixel G K else 0 else 0) from ?_]
 · split_ifs
   · constructor
     · intro t y;simp_rw [happens, WilsonStartup.coeff_adjoint]
     intro z y; simp_rw [happens]
     let V(s:ℝ)(j:Fin K):=G.adjoint (G.lieExp (s • z)) (y j)
     have he:HasDerivAt V (fun j=>G.ad z (y j)) 0:=hasDerivAt_pi.mpr fun j=> Extra.WeakScaling.Color.tangent ..
     let T:=Tensor.coeff (inK G) K 0
     have hf:HasDerivAt (fun s=>T (V s)) ((T.linearDeriv (V 0)) (fun j=>G.ad z (y j))) 0:= T.hasFDerivAt _|>.comp_hasDerivAt 0 he
     have hg:=hf.unique (show HasDerivAt (fun s=>T (V s)) 0 (0:ℝ) by unfold V T; simp_rw [coeff_adjoint];exact hasDerivAt_const ..)
     have H:V 0=y:=by funext i; unfold V; rw [zero_smul,G.mat_lieExp_zero,G.adjoint_one]
     rwa [H,ContinuousMultilinearMap.linearDeriv_apply] at hg
   all_goals exact (dressed G K).zero_mem
 funext y;change prize G K (lyre x y)=_
 rw [protectedR _ i]; simp only [lyre,Prod.ext_iff];split_ifs <;> rfl


end YM.RG08.Crown
