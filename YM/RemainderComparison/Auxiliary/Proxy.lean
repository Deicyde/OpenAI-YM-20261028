import YM.RemainderComparison.Auxiliary.Court
import YM.RemainderComparison.Exchange.Escrow
/-!
 # Enrollment of uncut T-moment polynomial as proxy on X halo.

 C magma finite analytic marker masses at input. Unrestricted powers retained for
 quotient/log. Output exact representative is `Aux.scaled_l` and `model` separate;
 this projection does NOT assert existence of support-index data on other tori,
 or identification with independent Bulk.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Aux
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext.Repeat Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.Scheduling ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Sienna Fare Germ Token
open YM.RemainderComparison.Exchange -- name collision
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {p q w t : ℝ→ℝ}
variable {r j n : ℕ}
variable {c f : Side} {S : StepData c f}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (T : Tube G S) (F : Forest S.ratio) (Θ : ChartRatio G) (k : S.Choices) (ρ : Bid.Dir G c→AxisChart G F)
local notation "Q₀" => Lapis.gram F T.up T.high ρ k
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "Y" => Poll.Body (Precision.Key F G)

def model (U:ℝ×Xs→Y→E) (n : ℕ) := Germ.early ((Q₀) 0)⁻¹ (combo T F Θ k ρ U) n
lemma model_anchor (U:ℝ×Xs→Y→ℝ) (n : ℕ) (x:Xs) (h:∀ z,U (0,x) z=1) : model T F Θ k ρ U n (0,x)=1 := by
  unfold model early; rw [Trace.polyeval_zero]; unfold warrant
  have hh i : Trace.coefficient (fun x=> combo T F Θ k ρ U x i) 0 x=1:= by
    unfold Trace.coefficient; rw [Nat.factorial_zero,Nat.cast_one,inv_one,one_smul]; change Germ.primary _ _ _ _ _ _ * U (0,x) i=1; rw [h, Germ.anchor,one_mul]
  simp_rw [hh]; simp
lemma tariff_rate (j k : ℕ) (hf: Reserve G L p) : Reserve G L fun x=> Trace.tariff j k (p x):=
    Reserve.mul (Reserve.mul (Reserve.const _) hf) (Reserve.const _)

/-! The larger k requirement here enables smooth accounting of f_≤k as a POLYNOMIAL
 with data, even outside its truncation support. -/
theorem paying (G : Gauge) (L : Side) (K : KernelChoices) {a d α:ℝ} (ha:0<a) (hd:0<d) (w q p f s: ℝ→ℝ) (hw:Bolt G L w) (hq:Reserve G L q) (hp:Reserve G L p) (hf:Reserve G L f)
    (hr:Rate G L α s) (hj : j+(r+1)+r ≤ n) (l : ℕ) :
    ∃ H: ℝ→ℝ, Reserve G L H ∧ ∀ᶠ t in atTop, let v:= Access.apron G L t; let u:= p t; let D:= wick G L d t
      ∀ (c f':Side) (S:StepData c f') (T: Tube G S) (F: Forest S.ratio) (Θ: ChartRatio G) (k:S.Choices) (ρ:Bid.Dir G c→AxisChart G F) (B:BudgetPoint) (β:ℝ) (x:Positions (Uniform.Primary c G)) (O:Teller G), Weather T F Θ k ρ B β d t a (w t) u (q t) K O n x L →
      ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E] [CompleteSpace E] (P:Config G f'→E) (U:ℝ×Positions (Uniform.Primary c G)→Poll.Body (Precision.Key F G)→E),
        Playing F ρ β U P x D (furl G L t) u v (f t) (s t) n l →
        Queue (model T F Θ k ρ U r) (scaled_l T F Θ k ρ B β P) (gStep β) x v u j r (H t) ∧
        ∀ (i m:ℕ), m+i ≤ n → ∀ x:Positions (Uniform.Primary c G), ‖x‖ < p t → Brush m (H t) 1 (warrant (Lapis.gram F T.up T.high ρ k 0)⁻¹ (combo T F Θ k ρ U) i) x := by
  let c':= (a/2)⁻¹; let N:=(n+2)*n; let φ:ℝ:=-((r+1:ℕ):ℝ)/2-1; let j':=j+(r+1)
  obtain ⟨v',hp',hv⟩:= inside G L n (by omega) q (wick G L d) p hq (Reserve.wig d) hp
  let V t:=v' t*f t*3^n
  have hf' : Reserve G L V:= (hp'.mul hf).mul (Reserve.const _)
  obtain ⟨Y',hY,H⟩:= runway G L r j n (N+l) hf' hw c' d hd (inv_pos.mpr (by positivity)) (by omega)
  let C t:=1+Y' t; let g₁ t:= Trace.tariff r j' (Y' t)
  refine ⟨fun t=> C t+g₁ t, ((Reserve.const 1).add hY).add (tariff_rate _ _ hY),?_⟩
  filter_upwards [curtain G L K ha hd w q p f s hw hq hp hf hr (show j+1≤ n by omega) l (φ:=φ), hv,H, Access.exchange (G:=G) (L:=L) φ (r+1) (by unfold φ; linarith) Rate.power,Access.wide hp.rate,Delay.shift_pos G L] with t hx hF hH hφ hv hW v u D c f' S T F Θ k ρ B β x O he E _ _ _ _ P U hU
  have hO:= he.canvas; have hP:=he.paint
  let Q':= Lapis.gram F T.up T.high ρ k; let Ξ:= Germ.primary (Lapis.table F k T.up T.high) (Lapis.mist F Θ T.up) (Lapis.orbit F ρ) Q'; let μ:= (Q' 0)⁻¹
  have hy: 0< Sienna.furl G L t:=Real.rpow_pos_of_pos hW _
  have ht: ‖x‖<u:= (le_add_of_nonneg_right hy.le).trans_lt he.cabin
  have hc:= hP.core
  have hh: Cloud Ξ D v u n N (v' t):= hF _ _ _ _ _ _ ((norm_nonneg _).trans_lt ht) hP.core
  have hQ: Cloud (combo T F Θ k ρ U) D v u n (N+l) (V t):= hh.mix hU.tagGerm
  have hM: μ.PosDef:= (hc.gram _ (show ‖(0:Positions (Uniform.Primary c G))‖< eaves G L t from norm_zero.trans_lt hc.pos)).1.inv
  have hk : Germ.Contract μ c' := hP.inverse
  let g:= gStep β
  have hl := lane T B he.feed he.patch; have hβ:=hv.2 β hl
  have hd: (g,x)∈Germ.patch (Positions (Uniform.Primary c G)) v u:= (patch_test ..).2 ⟨(Real.norm_of_nonneg hβ.1.le).trans_lt hβ.2, ht⟩
  have hf' z (hz:‖z‖ < u):= hH β hl u _ _ _ (Lapis.countsK F _ hO.overall) μ hM hk _ hQ z hz
  have hq:= (hf' _ ht).2 0 0 (Nat.zero_le _)|>.nonneg; have hr:0≤ C t:= add_nonneg zero_le_one hq
  let W:=model T F Θ k ρ U r
  have hS z (hz:z∈Germ.patch (Positions (Uniform.Primary c G)) v u) : Brush j' (g₁ t) 1 W z :=
    let h:= (patch_test ..).1 hz; Trace.currency _ (h.1.le.trans (hv.1.2.1.le.trans hv.1.2.2.1.le)) (fun i hi=>(hf' _ h.2).2 _ _ (by unfold j'; omega))
  have hS':= hS _ hd |>.nonneg
  let e:= scaled_l T F Θ k ρ B β P
  let V₀ z:= coupon μ (combo T F Θ k ρ U) D (g,z)
  have hw : Brush j (g^(r+1)) 1 (fun y=> e y - V₀ y) x:= (hx _ _ S T F Θ k ρ B β _ _ he E P U hU).climb ((le_abs_self _).trans (hφ β hl)) le_rfl
  refine ⟨⟨add_nonneg hr hS',hd,hβ.1,fun y hy=> (hS y hy).climb (le_add_of_nonneg_left hr) le_rfl,?_⟩,fun i m hm z hz=> ((hf' z hz).2 m i hm).climb ((show Y' t ≤ C t from le_add_of_nonneg_left zero_le_one).trans (le_add_of_nonneg_right hS')) le_rfl⟩
  have hp := hw.gathering (hf' x ht).1
  refine (hp.climb ?_ le_rfl).shimmy ?_
  · have h : 0<g:= hβ.1
    rw [mul_add]; apply le_trans _ (le_add_of_nonneg_right (mul_nonneg (by positivity) hS')); unfold C; rw [mul_add,mul_one]
  exact Eventually.of_forall fun y=> by change e _-W (g,y)= e _-V₀ _+(V₀ y-W (g,y)); abel
end YM.RemainderComparison.Aux
