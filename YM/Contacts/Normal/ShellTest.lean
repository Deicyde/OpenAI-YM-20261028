import YM.Contacts.Normal.CompactReserves

/-! # Costs of testing at one shell, including the tail

A normal test at parent scale `r` used at shell size `r*a`. The subtraction length `s` can be fixed or eventually small. Shell constants do not depend on `s`. Require `r ≤ B*s` for the test estimates; this includes the fixed-subtraction testing for scaling degree and the running-length tests. Also only use the estimate for the projection tail up to `r*a ≤ B*s`. Keep the full scaling seminorm in *all x-variables*.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Normal
open Function Filter Set Metric MeasureTheory Submodule MultipleContact Panel
open scoped Topology BigOperators Classical ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
variable (K : Submodule ℝ E) {m n : ℕ}

/-- Shell of radial-length units. -/
def sun (r : ℝ) := {x:E | ‖K.starProjection x‖∈Icc (r/2) (2*r)}
lemma closed_sun (r : ℝ) : IsClosed (sun K r):= isClosed_Icc.preimage K.starProjection.continuous.norm

def vanishFactor (m : ℕ) (a : ℝ) := if a ≤ 1 then a^(m+1) else a^m
lemma vanish_pos (m : ℕ) {a : ℝ} (ha : 0 < a) : 0 < vanishFactor m a:= by unfold vanishFactor; split <;> positivity
private def normedCut (s : ℝ) (x : E) := (window K 1).val (s • x)
private lemma priced_cut (T : Set E) (hT : IsCompact T) (B : ℝ) (n : ℕ) : ∃ H ≥(1:ℝ),∀ u : ℝ, u∈ Icc 0 B → Jet n T (normedCut K u) H := by
  let f (p:E×ℝ):= normedCut K p.2 p.1; have hf : ContDiff ℝ ∞ f := (infSmooth _).comp (contDiff_snd.smul contDiff_fst)
  obtain ⟨c,hc,h⟩:= controls hf (hT.prod (isCompact_Icc (a:=0) (b:=B))) n
  exact ⟨c,hc,fun t=> slice_bill hf _ t h⟩
private lemma affordable (T : Set E){B p c a : ℝ} (hp : BillOn K n m B p T) (hp' :1≤ p)
     (hU : T⊆ sun K 1) {f : SmoothTests E} (hf : Jet (n+m+1) univ f.val c)
     (he : tsupport f.val ⊆ {x:E| ‖K.starProjection x‖ ≤ B/2}) (ha : 0<a) : Jet n T (f.val ∘ slide K a) (p*c):=by
     by_cases hc:a ≤ B; exact hp.active hf a ⟨ha.le,hc⟩
     have ht := hf.pos; have hL :0<p:=zero_lt_one.trans_le hp'; apply Jet.near (f:=fun _=> (0:ℂ)) (show Jet n T _ (p*c) from ⟨by positivity, fun i _ x hx=>by simp only [show (fun _:E=> (0:ℂ))=0 from rfl]; simp [mul_nonneg hL.le ht]⟩)
     intro x hx; have hw: slide K a x∉ tsupport f.val:= fun h=> not_le_of_gt (by
          rw [slip,norm_smul,Real.norm_eq_abs,abs_of_pos ha]; exact (div_lt_div_of_pos_right (not_le.mp hc) two_pos).trans_le (by
            have hs:= mul_le_mul_of_nonneg_left (hU hx|>.1) ha.le; linarith only [hs]) : B / 2 < ‖K.starProjection ((slide K a) x)‖) (he h)
     symm; exact ((slide K a).continuous.tendsto x).eventually (notMem_tsupport_iff_eventuallyEq.mp hw) -- lhs const
-- remove unused parameters
private lemma tiny (T : Set E) (hU : T⊆ sun K 1){s : ℝ} (hs : 0 ≤ s)(hs':3*s ≤ 1): ∀ x∈T, normedCut K s =ᶠ[𝓝 x] fun _=>(1:ℂ) := by
  intro x hx; filter_upwards [(K.starProjection.continuous.norm).continuousAt (x:=x) |>.tendsto.eventually (p:=fun x=>x<3) (gt_mem_nhds (by linarith only [(hU hx).2]))] with y hy
  unfold normedCut; change (↑(cutoff 1 (K.starProjection _)):ℂ)=1; rw [MultipleContact.cutoff_eq_one zero_lt_one (?_),Complex.ofReal_one]
  rw [map_smul,norm_smul,Real.norm_of_nonneg hs]; exact le_trans (mul_le_mul_of_nonneg_left (le_of_lt hy) hs) (by linarith only [hs'])

/-- Uniform budget for each projection in running or fixed s regime. -/
lemma compact_deviation (n m : ℕ){T : Set E}(hT : IsCompact T) (hU : T⊆ sun K 1) (B : ℝ) (hB : 1≤ B) :
  ∃ X ≥ (1:ℝ),∀ (a : ℝ)(ha:0 < a) {r s c : ℝ} {A : E≃L[ℝ] E}(f : SmoothTests E), Proper A r K → 0<r → 0<s →
    (r*a)/s ≤ B → r ≤ B*s →
    tsupport (composed A f).val ⊆ {x | ‖K.starProjection x‖ ≤ B/2} → Jet (n+m+1) univ (composed A f).val c →
       Jet n T (composed ((resize K a ha.ne').trans A) (deviation K s m f)).val (X*c*(vanishFactor m a)):= by
   obtain ⟨p,hp,h⟩:= from_compact K T hT B (zero_le_one.trans hB) m n; obtain ⟨d,hd,hH⟩:= priced_cut K T hT B n
   let R:=3*B; let X:= p+2^n*d*((m+1:ℝ)*p)
   have hp':0<p:= zero_lt_one.trans_le hp; have hd':0<d:=zero_lt_one.trans_le hd; have hZ : p ≤ X:= le_add_of_nonneg_right (by positivity); have hR : 1 ≤ R:= by unfold R; linarith; -- one factor
   refine ⟨X* R^(m+1),one_le_mul_of_one_le_of_one_le (hp.trans hZ) (one_le_pow₀ hR),fun a ha r s c A f hw hr hs hL hk hv hQ=>?_⟩ -- binder maybe lambda implicits
   rw [cash_a K _ _ hw]
   let g:=composed A f; let u:=r*a/s; let v:=normedCut K u
   change Jet n T ((g.val ∘ (slide K a))-v*((jet K m g).val ∘ slide K a)) _
   have hc:= hQ.pos; have Hv : ContDiff ℝ ∞ v:= (infSmooth (window K _)).comp (contDiff_id.const_smul u); have hx :0 < u:=by unfold u; positivity
   have H₁ : ContDiff ℝ ∞ (g.val ∘ slide K a):= (infSmooth _).comp (slide K a).contDiff
   have H₂ : ContDiff ℝ ∞ ((jet K m g).val ∘ slide K a):= (infSmooth _).comp (slide K a).contDiff
   have HL:= affordable K T h hp hU hQ hv ha
   have hv':= (whole_bill K m n B h hp'.le ha hQ)
   let w:=(max 1 a)^m; have hw:1≤ w:= one_le_pow₀ (le_max_left ..); have hN:= HL.sub ((hH u ⟨hx.le,hL⟩).times hv' Hv H₂) H₁ (Hv.mul H₂); have he : Jet n T ((g.val ∘ (slide K a))-v*((jet K m g).val ∘ slide K a)) (X*c*w):=hN.mono (by unfold X w; nlinarith only [le_mul_of_one_le_right (mul_nonneg hp'.le hc) hw])
   have hX:0 < X:= hp'.trans_le hZ
   have hY:X≤ X*R^(m+1) := le_mul_of_one_le_right hX.le (one_le_pow₀ hR)
   by_cases H:a ≤ 1; swap
   · rw [vanishFactor,if_neg H]; unfold w at he; rw [max_eq_right (not_le.mp H|>.le)] at he; exact he.mono (by gcongr)
   rw [vanishFactor,if_pos H]; unfold w at he; rw [max_eq_left H,one_pow,mul_one] at he
   by_cases hb : 3*u ≤ 1
   · apply ((h.remainds hQ a ⟨ha.le,H.trans hB⟩).near ?_).mono; · gcongr; exact hZ.trans hY
     intro x hx'; filter_upwards [tiny K T hU hx.le hb x hx'] with y hy; change g.val _- (jet K m g).val _ = g.val _- v y *_; change v y=1 at hy; rw [hy,one_mul]; rfl
   have hT : 1 ≤ R*a:=by
      have hx:u ≤ B*a:=by apply (div_le_iff₀ hs).2; linarith only [mul_le_mul_of_nonneg_right hk ha.le]
      linarith only [hx,not_le.mp hb] -- unfold R?
   refine he.mono ( (le_mul_of_one_le_right (mul_nonneg hX.le hc) (one_le_pow₀ hT (n:=m+1))).trans_eq (?_)); rw [mul_pow]; ring
end YM.Contacts.Normal
