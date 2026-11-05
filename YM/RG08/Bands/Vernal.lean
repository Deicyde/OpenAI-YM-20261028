import YM.RG08.Bands.Duel
/-!
# At time one. Keep the scale factors outside of the Born sum.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Bands
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {I α :Type} [Fintype α]{u:List I}{a:I→ℕ}{F V:Screed ℝ α}{S:Canticle α}{U:I→ Screed ℝ α}{K:Row α α}{p:Option Side}{t k n e τ r:ℕ}{m c:Side}
section time
variable {P Q : HeatS α}
def endP (τ:ℕ)(P: HeatS α)(j:ℕ):Spine ℝ α:= ∑ i∈range (windows τ j+1),P i j
lemma reels_sink (h:Reels τ P): Sails τ (endP τ P):= swung fun i=> Loomed.sum fun j _=> (h j).thin i
lemma end_eval (h:Reels t P)(o:Site c)(e:ℕ): large o (t+e) (endP t P e) = ∑ i∈range (windows t e+1),glee t o P i e:= spool_group _ (fun j _=> (h j).thin e) _
lemma end_w (τ:ℕ)(p:Option Side):endP τ (murmur p K S F)= washed τ p K S F := by funext i j; unfold endP washed; rw [Finset.sum_apply]
lemma end_sub (τ:ℕ)(P Q:HeatS α): endP τ (P-Q)=endP τ P-endP τ Q:= by funext i; simp only [endP, Pi.sub_apply, Finset.sum_sub_distrib]
lemma pace_l (h:Sails τ F)(he:Whole K)(hp:Gets S) : Last τ (murmur p K S F):= by
   intro i j hv; ext1 k; change _=0; refine not_ne_iff.mp (mt (murmur_degree he (fun i j=> hp.2 i j|>.1) hp.1 h.tide h.budget) ?_); unfold windows at *; omega
lemma last_start (α:Type): Last 0 (upstart α):=by
  intro i j h; unfold upstart; rw [if_neg (by unfold windows at *; omega)]; rfl
lemma borne_last (h: Last τ P)(hp: Last t Q) : Last (τ+t) (borne P Q):= by
   intro i j hh
   refine sum_eq_zero fun b hb=> sum_eq_zero (s:=wheel j) fun k hk=>funext fun r=>?_
   change _=0; apply sum_eq_zero; intro v hv; by_cases hx:windows τ k.1 < b.1; · rw [h _ _ hx]; change grant _ (braidV (0:Shale α v.1) _)=_; rw [braid_none,grant_zero]
   have ht : windows t k.2 < b.2:= by have hb:=mem_antidiagonal.mp hb; have hk:=mem_antidiagonal.mp hk; unfold windows at *; omega
   rw [hp _ _ ht]; change grant _ (braidV _ (0:Shale α v.2))=_; rw [braid_no, grant_zero]
lemma cast_last {F:I→HeatS α}(h:∀ i∈u,Last (a i) (F i)): Last (loadᵣ a u) (castM F u):= by
   induction u with
   | nil=> exact last_start α
   | cons b u ih=> exact borne_last (h b List.mem_cons_self) (ih fun i hi=> h i (List.mem_cons_of_mem _ hi))
lemma unrolled (h:Sails τ F)(hp:Sails τ V)(ht:∀ i,∀ m:Side,large (0:Site m) (τ+i) (F i)=large 0 (τ+i) (V i)): F=V:= by
   funext i j
   apply Tidy.uniquely (h.tide i j) (hp.tide i j); intro m

   have he : glee τ (0:Site m) (fun _=> F)=glee τ 0 (fun _=> V):= funext fun n=>funext fun k=> ht k m
   exact glee_stanza (fun _ => h) (fun _=> hp) _ he 0 i j
lemma pace_z (h:Reels τ P)(hz:Last τ P)(c:Side)(i:Site c)(k n:ℕ)(hk:windows τ n < k) : glee τ i P k n=0:= by unfold glee large; rw [hz k n hk]; simp
lemma borne_fin (h: Reels τ P)(hp:Reels t Q)(hv: Last τ P)(hk: Last t Q): endP (τ+t) (borne P Q)= gust (endP τ P) (endP t Q) := by
   have hM :=borne_r h hp
   apply unrolled (reels_sink hM) (braid_s (reels_sink h) (reels_sink hp))
   intro e m; let x:Site m:=0; let F:= glee τ x P; let G:=glee t x Q
   rw [end_eval hM 0 e,sing_k (reels_sink h) (reels_sink hp),tempo_b h hp]; unfold billow dancing
   have hx i : ∑ b∈wheel i,∑ a∈wheel e,F b.1 a.1 * G b.2 a.2=∑ a∈wheel e,∑ b∈wheel i,F b.1 a.1 * G b.2 a.2:= sum_comm
   change (∑ i∈_,∑ b∈wheel i,∑ a∈wheel e,F b.1 a.1 * G b.2 a.2) = _; simp_rw [hx]; rw [sum_comm]; refine sum_congr rfl fun a ha=> ?_
   have hm : windows (τ+t) e=windows τ a.1+windows t a.2:= by unfold windows; have hk:=mem_antidiagonal.mp ha; omega
   symm; rw [end_eval (P:=P) h 0 (a.1),end_eval (P:=Q) hp 0 a.2] -- maybe
   change (∑ i∈range (windows τ a.1+1), F i a.1)*(∑ j∈range _,G j a.2)=_
   rw [hm,Finset.sum_mul]; simp_rw [Finset.mul_sum]; exact triangle_sum _ _ _ fun i j he=> ⟨Nat.lt_add_one_iff.mpr (le_of_not_gt (fun hB=> he (by rw [show F i a.1=_ from pace_z h hv _ _ _ _ hB,zero_mul]))),Nat.lt_add_one_iff.mpr (le_of_not_gt (fun hy=>he (by rw [show G j a.2=0 from pace_z hp hk _ _ _ _ hy,mul_zero])))⟩
lemma end_unit (α:Type):endP 0 (upstart α)=spine_one α:= by
    funext i j; unfold endP; simp only [Finset.sum_apply]; rw [sum_eq_single_of_mem 0 (mem_range.mpr (by omega)),upstart,if_pos rfl]
    intro b _ hb; rw [upstart,if_neg hb]; rfl
lemma cast_end (hp:Whole K)(hs:Gets S)(hx:∀ i∈u,Sails (a i) (U i)) : endP (loadᵣ a u) (birth p K S U u)=washed (loadᵣ a u) p K S (castF U u) - castF (fun i=> washed (a i) p K S (U i)) u := by
   unfold birth; let Z i:=murmur p K S (U i)
   rw [end_sub,end_w]; congr 1
   change endP _ (castM Z u)=_
   induction u with
   | nil=> exact end_unit _
   | cons i v ih=>
     have hu:=hx i List.mem_cons_self; have h j hj:=hx j (List.mem_cons_of_mem _ hj)
     have he (j)(hj:j∈v): Reels (a j) (Z j):= dressing (h j hj) hp hs
     change endP (a i+ loadᵣ a v) (borne (murmur p K S (U i)) (castM Z v))= gust (washed _ _ _ _ _) (castF _ v)
     rw [borne_fin (dressing hu hp hs) (cast_r he) (pace_l hu hp hs) (cast_last (F:=Z) (fun i hi=>pace_l (h i hi) hp hs)),end_w,ih h]
end time
end YM.RG08.Bands
