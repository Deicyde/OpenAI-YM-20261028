import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Ledger
import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Licensed

/-!
# Deliver E μ estimates to the actual pricing data

We don't ask for additional regularity on labels. On the fixed H,
ports, V and Y record take only derivatives of extensions (receipts
include pointwise correspondence for ALL records with correct V flags).
Compatible with covariance on the *same* panels and path data. Signs are
for `Rows.eta = -g⁻¹ • (Q *ᵥ μ+b)`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.SectorAffine.Offset
open Filter Function Lattice Wilson RG Precision Pressure Tree Exterior Bloch
open YM.Next YM.Next.Fluctuations YM.Next.SectorChange YM.Next.SectorChange.Rows
open YM.Push.Uniform (bolt Allows)
open YM.Push.SectorMeasure
open YM.FreeResolvent (Mark Bundle native)
open YM.FreeResolvent.TestD Matrix
open scoped Topology ContDiff BigOperators InnerProductSpace Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {P : Patch} {T : Tube G S} {F : Forest S.ratio} {A : Stores S}
    {V : Config G c} {k : S.Choices} {x B η δ d γ v l M N C t : ℝ} {n : ℕ}

section quantities
variable (T : Tube G S) (x : ℝ) (k : S.Choices) (A : Stores S) (F : Forest S.ratio) (q : Chi) (d : ℝ)
    (Y : LinkArray G (Frozen A x F)) (V : Config G c)

def b := (move T x V k (shots S x) A F)ᵀ *ᵥ f0 T x A F k V q d Y

def mean := -(Schur.per (panels A F) (Rows.gram T x V k (shots S x) A F)).transpose *ᵥ b T x k A F q d Y V

def residual := Rows.gram T x V k (shots S x) A F *ᵥ mean T x k A F q d Y V + b T x k A F q d Y V

lemma reads_actual (h : f0 T x A F k V q d Y = Rows.source T x V k (shots S x) A F q d Y) :
    b T x k A F q d Y V = Rows.blame T x V k (shots S x) A F q d Y ∧
    mean T x k A F q d Y V = meanLog A F T x V k q d Y ∧
      ∀ g : ℝ, Rows.eta T x V k (shots S x) A F q d Y (mean T x k A F q d Y V) g = -g⁻¹ • residual T x k A F q d Y V := by
  unfold meanLog Rows.eta residual mean b Rows.blame; simp only [h]; tauto
end quantities

section application
variable {q : Chi} {Y : LinkArray G (Frozen A x F)}

/-- On any frozen values *simultaneously* in these budgets. Need t-scaled
commands since these also bound Y-dependence terms. Budgets apply with
χ choice kept fixed before scheduling tail. Includes exact value agreements
on this sector's recorded branches. This isn't a `SmoothNN` assertion
nor an extension of measure. -/
structure Shift (n : ℕ) (x d v ε M : ℝ) (T : Tube G S) (F : Forest S.ratio) (A : Stores S) (V : Config G c)
    (k : S.Choices) (q : Chi) : Prop where
  okay : f0 T x A F k V q ε = Rows.source T x V k (shots S x) A F q ε
  corners (Y : LinkArray G (Frozen A x F)) :
    Parcel 0 (Wisps.down S) d n (fun z => f0 T x A F k (pulse x V z) q ε Y) (M*fiery G x S.patch.L)
  steps (Y : LinkArray G (Frozen A x F)) :
    let t := fiery G x S.patch.L
    let p := Wisps.front A F (G:=G) (x:=x)
    Parcel 0 p d n (b T x k A F q ε Y ∘ pulse x V) (M*t) ∧
    Parcel 0 p d n (mean T x k A F q ε Y ∘ pulse x V) (M*t) ∧
    Parcel 0 p d n (Offset.residual T x k A F q ε Y ∘ pulse x V) (M*t*Real.exp (-v*radiusB x))

private lemma deliver {a : ℝ} (hm : 0<M) (hn : 0<N) (hd : 0 ≤ d) (hδ : d≤δ) (hv : n*d ≤ δ) (hs : 0 ≤ temp x)
    (ht : temp x ≤ 1) (hη : 0 < η) (h : KernelJets n δ v η l M A F T x V k 0) (hc :
      Parcel 0 (Wisps.down S) d n (fun z => f0 T x A F k (pulse x V z) q a Y) (N*fiery G x S.patch.L)) :
    let Q := 2^n*(N*M)
    let J := 2^n*(Q*M)
    let E := 2^n*(J*M)
    let p := Wisps.front A F (G:=G) (x:=x)
    let t := fiery G x S.patch.L
    Parcel 0 p d n (b T x k A F q a Y ∘ pulse x V) (Q*t) ∧
    Parcel 0 p d n (mean T x k A F q a Y ∘ pulse x V) (J*t) ∧
    Parcel 0 p d n (Offset.residual T x k A F q a Y ∘ pulse x V) (E*t*Real.exp (-v*radiusB x)) := by
  intro Q J E p t
  let f := b T x k A F q a Y ∘ pulse x V
  let g := mean T x k A F q a Y ∘ pulse x V
  let P (y) := pickedPi A F T x V k 0 (temp x • (y:PriceCoords G c))
  let U (y : PriceCoords G c) := profileGram T x V A F k (temp x • y)
  have he (y : PriceCoords G c) : g y = -(P y)ᵀ *ᵥ f y := by
    simp only [P,g,f,pickedPi,panelPi,zero_smul,add_zero]; rfl
  have ht' : 0 ≤ fiery G x S.patch.L := temp_nonneg _
  have hQ : 0 ≤ Q*t := mul_nonneg (show 0 ≤ Q by unfold Q; positivity) ht'
  have hD := polar_compress h.moves.transpose hs ht
  have hb : Parcel 0 p d n f (Q*t) :=
    (hc.deliver (mul_nonneg hn.le ht') hD hm.le hd hδ hv).mono le_rfl (le_of_eq (by unfold t Q; ring))
  have hU : Polar 0 p p U n δ M := polar_compress h.gramJets hs ht
  have hr := (h.windowJets 0 le_rfl).polar hm.le le_rfl
  rw [show drain 0=1 by simp [drain],mul_one] at hr
  have hPi : Polar 0 p p (fun y => (P y)ᵀ) n δ M := (polar_compress hr hs ht).transpose
  have hJ : Parcel 0 p d n g (J*t) := by
    apply (((hb.deliver hQ hPi hm.le hd hδ hv).mono le_rfl (le_of_eq (by unfold t J; ring))).nonnegated).glue
    exact Filter.Eventually.of_forall fun y => by
      rw [he,Matrix.neg_mulVec]; rfl
  refine ⟨hb,hJ,?_⟩
  let K := Real.exp (-v*radiusB x)
  have ht := h.closenessJets 0 le_rfl
  rw [shift_zero,show drain 0=1 by simp [drain],one_pow,mul_one] at ht
  let W (y : PriceCoords G c) := ((P y)-(U y)⁻¹)ᵀ
  have hM : Polar 0 p p W n δ (M*K) := (polar_compress ht hs (by assumption)).transpose
  have hw : Parcel 0 p d n (fun y => W y *ᵥ f y) (J*t*K) := (hb.deliver hQ hM
    (mul_nonneg hm.le (Real.exp_pos _).le) hd hδ hv).mono le_rfl (le_of_eq (by unfold t J; ring))
  refine (((hw.deliver (by unfold J Q K; positivity) hU hm.le hd hδ hv).mono le_rfl
    (le_of_eq (by unfold E K; ring))).nonnegated).glue ?_
  have hη' : YM.FreeResolvent.Gap (U 0) η := by unfold U; rw [smul_zero]; exact h.solvency
  filter_upwards [germ_valid (A:=U) (hη'.shift 0 |>.unit_det (show 0<η+0 by positivity))
    hU.smooth.continuousAt] with y hy
  have hl : (U y).IsSymm := by unfold U profileGram Rows.gram Matrix.IsSymm; rw [Matrix.transpose_mul,Matrix.transpose_transpose]
  have hx : IsUnit (U y).det := by unfold Neat at hy; rwa [zero_smul,add_zero] at hy
  change -(U y *ᵥ (W y *ᵥ f y))=U y *ᵥ g y+f y
  rw [he]; unfold W
  rw [Matrix.transpose_sub,hl.inv.eq,Matrix.sub_mulVec,Matrix.neg_mulVec,Matrix.mulVec_neg, Matrix.mulVec_sub,
    Matrix.mulVec_mulVec (f y) (U y) (U y)⁻¹, Matrix.mul_nonsing_inv _ hx,Matrix.one_mulVec]; abel

theorem prices (G : Gauge) (P : Patch) (Pt : Teller G) (B : ℝ) (hB : 0<B) (q : Chi) (n : ℕ) (hP : P.Branches Pt.bind G) :
    ∃ r d d' v M N η l : ℝ, 0<r ∧ 0<d ∧ 0<d' ∧ 0<v ∧ 0<M ∧ 0<N ∧ 0<η ∧ 0<l ∧
    ∀ᶠ x : ℝ in atTop, 120 ≤ radiusB x ∧ ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P →
    100*(1+radiusB x) ≤ c.val → Pt.Funds S T → ∀ (A : Stores S) (F : Forest S.ratio) (V : Config G c),
    V∈eligible A G x → ∀ k : S.Choices,
      (∀ z : PriceCoords G c, ‖z‖≤r → Estimate n d' v η l N A F T x V k z) ∧
        Shift n x d v (B*fiery G x S.patch.L) M T F A V k q := by
  obtain ⟨d,M,hd,hM,H⟩ := f0_cost G P Pt q hB hP n
  obtain ⟨r,d',v,η,l,N,hr,hd',hv,hη,hl,hN,h'⟩ := estimates G P Pt hP n
  let Q := 2^n*(M*N)
  let A := 2^n*(Q*N)
  let W := 2^n*(A*N)
  let L := max (max M A) (max W Q)
  have h₁ : M ≤ L := (le_max_left M A).trans (le_max_left ..)
  have h₂ : A ≤ L := (le_max_right ..).trans (le_max_left ..)
  have h₃ : W ≤ L := (le_max_left W Q).trans (le_max_right ..)
  have h₄ : Q ≤ L := (le_max_right ..).trans (le_max_right ..)
  let s := min d (d'/(n+1:ℕ)); have hs : 0<s := lt_min hd (by positivity)
  have he : s+n*s ≤ d' := by
    have he := mul_le_mul_of_nonneg_right (show s≤_ from min_le_right d (d'/(n+1:ℕ)))
      (show 0 ≤ ((n+1:ℕ):ℝ) by positivity)
    rw [div_mul_cancel₀ d' (by positivity)] at he
    push_cast at he; linarith only [he]
  refine ⟨r,s,d',v,L,N,η,l,hr,hs,hd',hv,hM.trans_le h₁,hN,hη,hl,?_⟩
  filter_upwards [H,h',monitors G P.L] with x hx hp hh
  refine ⟨hp.1,?_⟩
  intro c f S T hT hF hP F F' V hV k
  have ht : 0 ≤ fiery G x S.patch.L := temp_nonneg _
  have h := hp.2 S T hT hF hP F F' V hV k
  obtain ⟨hy,hL⟩ := hx S T hT hP hF F' F V hV k
  refine ⟨h,⟨hy,(fun Y => Parcel.mono (hL Y) (min_le_left ..) (mul_le_mul_of_nonneg_right h₁ ht)),?_⟩⟩
  intro Y t p
  obtain ⟨ha,hb,hc⟩ := deliver hN hM hs.le ((le_add_of_nonneg_right (show 0≤n*s by positivity)).trans he)
    (show n*s ≤ d' by linarith only [hs,he]) hh.1.le hh.2.1 hη (h 0 (by simpa using hr.le)).toKernelJets
      ((hL Y).mono (min_le_left ..) le_rfl)
  exact ⟨ha.mono le_rfl (mul_le_mul_of_nonneg_right h₄ ht),hb.mono le_rfl (mul_le_mul_of_nonneg_right h₂ ht),
    hc.mono le_rfl (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h₃ ht) (Real.exp_pos _).le)⟩
end application

section normalize
variable {ι : Type} [Fintype ι] {a : ι → Site c} {H : Config G c → ι → ℝ}

/-- Convert to  polynomial powers around arbitrary o. Use explicit
flags branch for b, μ, affine eta. Ordinary left exp coordinates. -/
def Stipulates (p : ℕ) (a : ι → Site c) (k : ℕ) (t M : ℝ) (V : Config G c) (H : Config G c → ι → ℝ) :=
  let K := H ∘ increment V
  ContDiffAt ℝ k K 0 ∧
    ∀ (o : Site c) (l : List (Directions G c)), l.length ≤ k → Afford t p o l → ∀ i : ι,
      let r := (1+(separation (a i) o:ℝ))^p
      (r^l.length)⁻¹ * |jet id K l 0 i| ≤ M

lemma stipulation {h : ℕ} (hp : Parcel 0 a d n (H ∘ pulse x V) C) (hd : 0 < d) (ht : 0 < temp x) (hc : 0 ≤ C) :
    Stipulates h a n (temp x) (activation G n h d*C) V H := by
  have he := Parcel.activated_scale (H:=H ∘ field V) hp hd ht h hc
  rw [show (H ∘ field V) ∘ reader G c= H ∘ increment V from funext fun y => by simp only [Function.comp_apply,reader_field]] at he
  exact he

variable {a' : ℝ} {q : Chi}
lemma Shift.stipulated (h : Shift n x d v a' M T F A V k q) (hd : 0<d) (hm : 0≤M) (ht : 0<temp x)
    (p : ℕ) (Y : LinkArray G (Frozen A x F)) :
    let C := activation G n p d*M
    let t := C*fiery G x S.patch.L
    let a := Wisps.front A F (G:=G) (x:=x)
    (b T x k A F q a' Y V=Rows.blame T x V k (shots S x) A F q a' Y ∧ mean T x k A F q a' Y V=meanLog A F T x V k q a' Y) ∧
    Stipulates p (Wisps.down S) n (temp x) t V (fun V => f0 T x A F k V q a' Y) ∧
    Stipulates p a n (temp x) t V (b T x k A F q a' Y) ∧
    Stipulates p a n (temp x) t V (mean T x k A F q a' Y) ∧
    Stipulates p a n (temp x) (t*Real.exp (-v*radiusB x)) V (Offset.residual T x k A F q a' Y) := by
  intro C t a
  obtain ⟨hh,hj,hx⟩ := h.steps Y
  obtain ⟨hv,hv',-⟩ := reads_actual T x k A F _ _ Y V (congr_fun h.okay Y)
  have hk := mul_nonneg hm (show 0 ≤ fiery G x S.patch.L from temp_nonneg _)
  unfold t C; rw [mul_assoc]
  refine ⟨⟨hv,hv'⟩,stipulation (H:=fun V => f0 T x A F k V q a' Y) (h.corners Y) hd ht hk,
    stipulation hh hd ht hk,stipulation hj hd ht hk,?_⟩
  rw [mul_assoc]; exact stipulation hx hd ht (mul_nonneg hk (Real.exp_pos _).le)
end normalize
end YM.AnalyticBridge.SectorAffine.Offset
