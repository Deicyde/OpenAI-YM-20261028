import YM.RG08.Wax.Cove
/-! # Banner after folding pulses at time 1 exactly LOG
 -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Wax
open Function Filter Finset RG Stationary Quire Shade Bands Analysis Laurent Lattice Bloch Next.Free
open scoped Topology ContDiff BigOperators Matrix Classical
variable {I X:Type}[DecidableEq I][Fintype X][DecidableEq X]{m : ℕ→Side}{p: Option Side}{K:Row X X}{S:Canticle X}{τ:ℕ}
variable {a:I→ℕ}{F:Topaz I (Screed ℝ X)} {V: Topaz I (HeatS X)}

lemma gust_coin {U:Screed ℝ X}(h:Sails τ U) : gust U (spine_one X)=U:= by
  apply unrolled (τ:=τ) ?_ h
  · intro i j
    let P:HeatS X := fun n=> if n=0 then U else 0
    have hp : Reels τ P:= fun i=> by unfold P; split; exact h; exact swung fun i=>Loomed.zero
    let f:= glee τ (0:Site j) P
    have hh : glee τ 0 (borne P (upstart X)) = dancing f (glee 0 (0:Site j) (upstart X)):= by convert tempo_b hp reels_start (0:Site j) using 1; simp
    rw [glee_empty,dop_unit f] at hh
    have hx:borne P (upstart X) 0=gust U (spine_one X):= by rw [borne_z,show P 0=U from if_pos rfl,upstart,if_pos rfl]
    rw [← hx]; exact (congr_fun (congr_fun hh 0) i).trans (show f 0 i = _ from congr_arg (fun y: Screed ℝ X=> large (0:Site j) (τ+i) (y i)) (if_pos rfl : P 0=U))
  exact ((by simpa only [add_zero] using braid_s h (sails_start (α:=X))))
lemma themeBl {U:HeatS X}(h:Reels τ U): borne U (upstart X)=U:= by
  ext1 n; ext1 r; unfold borne; rw [sum_eq_single_of_mem (n,0) (show _ from mem_antidiagonal.mpr (add_zero n))];
  · rw [upstart,if_pos rfl,gust_coin (h n)]
  intro p hp he; have hx : p.2≠0:= by have ht:=mem_antidiagonal.mp hp; intro hh; refine he (Prod.ext (by dsimp; omega) hh)
  rw [upstart,if_neg hx]; ext1 j; simp [gust,Finset.sum_apply,spoolB,braid_no,grant_zero]

lemma maxhours (hF:∀ i,Sails (vanes a i) (F i))(hp:Whole K)(he:Gets S)(hx:F ∅=0)(hK:∀ c,(K.acts c)ᵀ=K.acts c)(T:Finset I) : Last (vanes a T) (pulse none K S F T) := by
   let U:= pulse none K S F; let B i:= banner i U borne (upstart X)
   have hw (i): Last (vanes a i) (B i):= by unfold B U; rw [prehistoric hp he hF hx hK]; exact pace_l (banner_z none hp he hF _) hp he
   have hu : Bulb (upstart X) borne U B:= bannerC _ _ _ borne_void (pulse_void F hp he hx)
   have hh i : Reels (vanes a i) (U i):= pulse_ok F hp he hF _
   induction T using strongInductionOn with
   | _ t ih=>
     change Last _ (U t); by_cases h:t=∅; · subst t; rw [hu.1]; exact fun _ _ _=>rfl
     intro n j ht; have hp:= congr_fun (congr_fun (congr_fun hu.2.2 t) n) j
     change (↑t.card:ℝ) • B t n j= _ at hp; unfold festival at hp; rw [Finset.sum_apply,Finset.sum_apply,hw _ _ _ ht,smul_zero,sum_eq_single (t,∅)] at hp
     · rw [hu.2.1,show borne (sons U t) (upstart X)= _ from themeBl (Reels.sm (hh t) (t.card:ℝ))] at hp
       exact (smul_right_injective _ (show (↑t.card:ℝ)≠0 from Nat.cast_ne_zero.mpr (card_ne_zero.mpr (nonempty_iff_ne_empty.mpr h)))) ((show (↑t.card:ℝ) • U t n j=0 from hp.symm).trans (smul_zero (↑t.card:ℝ)|>.symm))
     · intro i hi hx
       obtain ⟨hS,hL⟩:= (norms_par ..).1 hi
       have hr : i.1≠t:= by
          intro he'; apply hx; have hz:= par_count hi; exact Prod.ext he' (card_eq_zero.mp (by rw [he'] at hz; omega))
       have hp : Last (vanes a i.1) (U i.1):= ih _ (Finset.ssubset_iff_subset_ne.mpr ⟨by rw [hS]; exact subset_union_left,hr⟩)
       exact borne_last (show Last (vanes a i.1) (sons U i.1) from fun n j hj=> by simp [sons,hp n j hj]) (hw i.2) n j (by rw [← wind_cell a i hi]; exact ht)
     simp [norms_par]

lemma end_list (t : Finset I)(Z:I→HeatS X) : endP τ (∑ i∈t,Z i)= ∑ i∈t,endP τ (Z i) := by
    funext j; simp only [endP,Finset.sum_apply]; rw [sum_comm]
lemma end_scale (τ:ℕ)(s:ℝ)(v:HeatS X): endP τ (s • v)= s • endP τ v := by funext i; simp [endP,smul_sum]
lemma end_banner (hk:∀ i,Reels (vanes a i) (V i))(hp:∀ i,Last (vanes a i) (V i))(hv:∀ t, Last (vanes a t) (banner t V borne (upstart X))) (t: Finset I) : endP (vanes a t) (banner t V borne (upstart X))= banner t (fun i=>endP (vanes a i) (V i)) gust (spine_one X) := by
   induction t using strongInductionOn with
   | _ t ih=>
     rw [banner,banner]; by_cases h:t=∅; · subst t; rw [if_pos rfl,if_pos rfl,vanes_empty,end_unit]
     rw [if_neg h,if_neg h,end_scale,end_list]; apply congr_arg; refine sum_congr rfl ?_; intro i _
     rw [wind_cell a i.val (mem_filter.mp i.property).1];
     have he: Last (vanes a i.val.1) (sons V i.val.1):= fun n j hh=> by simp [sons,hp _ _ _ hh]
     rw [borne_fin (P:=sons V i.val.1) (Reels.sm (hk _) _) (walksR hk _) he (hv _), sons,end_scale,ih i.val.2 ?_]; rfl
     exact Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp (mem_product.mp (mem_filter.mp (mem_filter.mp i.property).1).1).2,fun v=>not_lt_of_ge (congr_arg Finset.card v).ge (shrank _ i.property)⟩

-- primary identity: exponential of output log is FULL Wick on exponential of input log (conditional denom).
theorem ceremony (hF:∀ i,Sails (vanes a i) (F i))(hp:Whole K)(he:Gets S)(hx:F ∅=0)(hK:∀ c,(K.acts c)ᵀ=K.acts c)(T:Finset I) :
   washed (vanes a T) none K S (banner T F gust (spine_one X))=banner T (fun i=>endP (vanes a i) (pulse none K S F i)) gust (spine_one X):= by
    rw [← end_w,← prehistoric hp he hF hx hK]; exact end_banner (pulse_ok F hp he hF) (maxhours hF hp he hx hK) (fun i=> by rw [prehistoric hp he hF hx hK]; exact pace_l (banner_z none hp he hF _) hp he) T
end YM.RG08.Wax
