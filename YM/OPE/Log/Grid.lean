import YM.OPE.Log.Pricing
import YM.OPE.Eye.Extract
/-! # Bracketing at a polynomial-log overshoot or undershoot -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log
open Filter Function Lattice RG Wilson MergeProof
open scoped Topology BigOperators
variable {G:Gauge}{C:Family G}{ι:Type*}{l: Filter ι}{T r:ι→ℝ}{a:ℝ} {A:Schedule} {m j:ι→ℕ}
-- ``at or above''
set_option quotPrecheck false
local notation "S"=> C.S
variable (hT:Tendsto T l atTop)

include hT in
lemma RateIs.offers {x r:ι→ℝ}(h:RateIs l T x a)(he:ValueStamp l T (fun i=>x i/r i))(hp:∀ᶠ i in l,0<r i) : RateIs l T r a:=by
    apply ((h.div (he.zeroCost hT)).swap (sub_zero _)).congr; filter_upwards [h.pos,hp] with i hi hf; field_simp -- include hT?

include hT
lemma previous (h: Height A l T m a)(hp:A.Gentle): Height A l T (fun i=> m i-1) a:=by
    let p i:=m i-1; have hu:Tendsto p l atTop:=tendsto_atTop.mpr fun i=> by filter_upwards [h.grows.eventually_gt_atTop i] with j hj; unfold p; omega
    let z i:= A.scale (p i); let u i:= A.scale (m i); have hg:Tendsto (fun i=> u i /z i) l (𝓝 1):=by
       have hz:= hp; unfold Schedule.Gentle at hz; have hF: ∀ᶠ i in l,z i ≠ 0:= ((A.divergent.comp hu).eventually_gt_atTop 0).mono fun i hi=> ne_of_gt hi
       refine (show Tendsto (fun i=> 1+ Real.log (A.block (p i)).val /z i) l (𝓝 1) from by simpa only [add_zero] using! ((hz.comp hu).const_add 1)).congr' ?_
       filter_upwards [hF,h.grows.eventually_gt_atTop 0] with i hi hx; unfold u; rw [← (show p i+1=m i from Nat.sub_add_cancel hx),A.scale_succ,add_div,div_self hi]
    refine ⟨hu, (show Tendsto (fun i => u i/T i /(u i/z i)) l (𝓝 a) from by simpa only [div_one] using! h.pace.div hg one_ne_zero).congr' ?_⟩; filter_upwards [(A.divergent.comp h.grows).eventually_gt_atTop 0] with i hi; simp only [div_eq_mul_inv,mul_inv_rev, inv_inv]; change 0<u i at hi; unfold p z at *; rw [show u i*(T i)⁻¹*(_*(u i)⁻¹) = A.scale (m i-1) * (T i)⁻¹*(u i*(u i)⁻¹) by ring,mul_inv_cancel₀ hi.ne',mul_one]
local notation "T'"=> fun i=>T i
variable (hr: RateIs l T r (-a))(he:Tendsto r l (𝓝 0))
include hr he
-- also brackets
private lemma boundaries (hp:A.Gentle) : ∃ j : ι→ℕ, Height A l T j a ∧ (∀ᶠ i in l, A.a (j i)< r i ∧ r i ≤ A.a (j i-1)) :=by
   classical
   let e i:=Real.log (r i)⁻¹
   have hh (i:ι):∃ m,e i<A.scale m := (A.divergent.eventually_gt_atTop (e i)).exists; let m i:= Nat.find (hh i); have hv i:e i < A.scale (m i):= Nat.find_spec (hh i); have hx (i:ι) (hp:0< m i): A.scale (m i-1) ≤ e i:= by apply le_of_not_gt; intro hl; have ht:m i ≤ m i-1:=Nat.find_min' (hh i) hl; omega
   have h' : Tendsto e l atTop:=by
      let v:=fun i=> -Real.log (r i); have hf:Tendsto r l (𝓝[>] 0):=tendsto_nhdsWithin_iff.mpr ⟨he,hr.pos⟩; exact (show Tendsto (fun i=>-(Real.log (r i))) l atTop from (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).comp hf).congr (fun i=>(Real.log_inv _).symm)
   have hE:Tendsto (fun i=> e i/T i) l (𝓝 a):=by simpa only [e,Real.log_inv,neg_div,neg_neg] using! hr.rate.neg
   have hy:Tendsto m l atTop:=tendsto_atTop.mpr fun j=> by filter_upwards [h'.eventually_ge_atTop (A.scale j)] with i hi using ((scale_mono A).le_iff_le.mp (le_trans hi (hv _).le))
   -- need Gentle
   let p i:=m i-1; have hu:Tendsto p l atTop:=tendsto_atTop.mpr fun i=> by filter_upwards [hy.eventually_gt_atTop i] with j hj; unfold p; omega
   let z i:= A.scale (p i); let u i:= A.scale (m i); have hg:Tendsto (fun i=> u i /z i) l (𝓝 1):=by
       have hz:= hp; unfold Schedule.Gentle at hz; have hF: ∀ᶠ i in l,z i ≠ 0:= ((A.divergent.comp hu).eventually_gt_atTop 0).mono fun i hi=> ne_of_gt hi
       refine (show Tendsto (fun i=> 1+ Real.log (A.block (p i)).val /z i) l (𝓝 1) from by simpa only [add_zero] using! ((hz.comp hu).const_add 1)).congr' ?_
       filter_upwards [hF,hy.eventually_gt_atTop 0] with i hi hx; unfold u; rw [← (show p i+1=m i from Nat.sub_add_cancel hx),A.scale_succ,add_div,div_self hi]
   have hF:Tendsto (fun i=>u i/e i) l (𝓝 1):=by
       refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
       · filter_upwards [h'.eventually_gt_atTop 0] with i hi using (one_le_div hi).mpr (hv i).le
       filter_upwards [hy.eventually_gt_atTop 0,(A.divergent.comp hu).eventually_gt_atTop 0,(A.divergent.comp hy).eventually_ge_atTop 0] with i hi hp hu using div_le_div_of_nonneg_left hu hp (hx i hi)
   refine ⟨m,⟨hy,?_⟩,?_⟩
   · refine (show Tendsto (fun i=> u i/e i*(e i/T i)) l (𝓝 a) from by simpa only [one_mul] using! hF.mul hE).congr' ?_; filter_upwards [h'.eventually_gt_atTop 0] with i hi; unfold u; field_simp
   filter_upwards [hy.eventually_gt_atTop 0,hr.pos] with i hi hr; have he' (i): A.scale i= -Real.log (A.a i):=Real.log_inv _; refine ⟨?_,?_⟩; · exact (Real.log_lt_log_iff (A.a_pos _) hr).mp ((neg_lt_neg_iff.mp (show -Real.log (r i)< -Real.log (A.a (m i)) from by rw [← he',← Real.log_inv]; exact hv i))) -- include hp arg
   refine (Real.log_le_log_iff hr (A.a_pos _)).mp (?_); apply neg_le_neg_iff.mp; rw [← Real.log_inv, ← Real.log_inv]; exact hx i hi

variable {W r' D} (L:LogPackage C W r' D)
include L
-- relative overshoot and undershoot
omit hr he in
lemma oneJump (h:Height S l T m a): ValueStamp l T (fun i=> C.S.a (m i-1)/ C.S.a (m i)):= by
    apply (blockWallet L hT (previous hT h (C.path.levels.fits.mesh))).congr; filter_upwards [h.grows.eventually_gt_atTop 0] with i hi; nth_rw 3 [← (show m i-1+1=m i from Nat.sub_add_cancel hi)]; rw [Schedule.a_step]; have he:= C.S.a_pos (m i-1); field_simp
lemma bracket_up : ∃ j : ι→ℕ, Height C.S l T j a ∧ (∀ᶠ i in l, C.S.a (j i)< r i ∧ r i ≤ C.S.a (j i-1)) ∧ ValueStamp l T (fun i=> r i/C.S.a (j i)):=by
    obtain ⟨j,hj,h⟩:=boundaries hT hr he (C.path.levels.fits.mesh); have hf := oneJump hT L hj; let x i:= C.S.a (j i); have hx i:0<x i:= C.S.a_pos _ ; have hu := h.mono (fun i hi=>(one_le_div (hx i)).2 (hi.1.le)) -- inference
    refine ⟨j,hj,h,⟨hr.pos.mono (fun i hi=> div_pos hi (hx i)), hf.up.of_le' (hr.pos.mono (fun i hi=>div_pos hi (hx i))) (h.mono fun i hi=> div_le_div_of_nonneg_right hi.2 (hx i).le), (ValueStamp.const hT one_pos).down.invLe (Eventually.of_forall fun _=> one_pos) hu⟩⟩
lemma bracket_down : ∃ j : ι→ℕ, Height C.S l T j a ∧ (∀ᶠ i in l, r i ≤ C.S.a (j i+1)) ∧ ValueStamp l T (fun i=> r i/C.S.a (j i)):=by
    obtain ⟨j,hj,h,hV⟩:= bracket_up hT hr he L
    let p i:=j i-1; have hp:= previous hT hj C.path.levels.fits.mesh; let m i:= p i-1
    refine ⟨m,previous hT hp C.path.levels.fits.mesh,?_,?_⟩
    · filter_upwards [h,hp.grows.eventually_gt_atTop 0] with i hi hv; unfold m; rw [Nat.sub_add_cancel (show 1 ≤ p i from hv)]; exact hi.2
    apply ((hV.div (oneJump hT L hj)).div (oneJump hT L hp)).congr; filter_upwards with i; have hx:= C.S.a_pos (p i); have hy:= C.S.a_pos (p i-1); have ht:= C.S.a_pos (j i); change r i/ C.S.a (j i) / (C.S.a (p i)/C.S.a (j i))/(C.S.a (p i-1)/C.S.a (p i))= r i / C.S.a (p i-1); field_simp
end YM.OPE.Log
