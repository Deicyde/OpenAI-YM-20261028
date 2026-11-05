import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.LocalLedger
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Patina


/-! # Loop purchases -- pre-L leading and common alpha only from the true limit.

Numerical price chosen on the WHOLE relevant patch (not among floating spectra or after p)
then during RLoops it pays even for all unscaled raw harmonic inputs in ANY appointed
kinematic path obeying its stage caps. Lease requests cannot pick their α again
for the real phase. The E $vvs$--$§continuum annulus$ bounds to actually get that
slope and charged+silent shape are NOT supplied. No perturbative result
on β at arbitrary Representatives; the same Rebuild/Program is still required
out back (choice must now succeed with these prices even if too punishing for sensible β gates).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Mural
open Paintings Filter Function Lattice Gauge RG Tree Precision Bloch Bid Enamel
    Extra.Iteration Calibration Macrame Wilson Exterior Input Push.Uniform Push
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} (s : RG.Supply.Sheet G) (P : RG.Patch) (Z : Stage)

/-- Pick once, may use even for virtual steps. Implicit coin comes from pre_order
for this whole family. Charges computable whenever s, Js and L known but
aren't contour or annular analyticity and those still must pay very different pre-L.
-/
def atlas : Paintings.Supply G P s.kernel Z :=
    ⟨Classical.choice (Push.Uniform.pre_order G _ _ _ _ (by have := Z.order_ge; omega)),s.has P,by have := Z.order_ge; omega⟩

variable {D : RG.Supply.Rolls s} {j : ℕ}

def sheet (D : RG.Supply.Rolls s) {j : ℕ} (hi : 4≤j) : Patch := ⟨D.L j,j,hi,(D.large j).size,(D.large j).odd⟩
-- monetary floors after D, Artillery universal h. independent of Z. Λ along schedule.
local notation "N" hi => atlas s (sheet s D hi) (s.profile j)
variable {s}
def pref (D : RG.Supply.Rolls s) (j : ℕ) := open scoped Classical in if h:4≤j then max 1 (((atlas s (sheet s D h) (s.profile j)).allowance)) else 1
lemma above_one (D : RG.Supply.Rolls s) (j : ℕ) : 1 ≤ pref D j := by unfold pref; split; exact le_max_left ..; rfl
def knot (D : RG.Supply.Rolls s) (j : ℕ) := open scoped Classical in if h:4≤j then
    max (0:ℝ) (if 0 < ((atlas s (sheet s D h) (s.profile j)).sights) then (atlas s (sheet s D h) (s.profile j)).sights else 1) else 1
lemma knot_pos (D : RG.Supply.Rolls s) (j : ℕ) : 0<knot D j := by unfold knot; split; apply lt_max_of_lt_right; split<;> positivity; exact zero_lt_one
lemma knot_low (hi : 4≤j) (hs : 0 < (atlas s (sheet s D hi) (s.profile j)).sights) : knot D j ≤ (atlas s (sheet s D hi) (s.profile j)).sights := by unfold knot; rw [dif_pos hi,if_pos hs,max_eq_right hs.le]

section Solo
variable {c f : Side} {S : StepData c f} (F : Forest S.ratio) (t : S.Choices) {R T : PathData G} {O : ChartRatio G}
    {ρ : Push.In G c→AxisChart G F} {α θ γ Λ : ℝ} {q : Clip}

/-- Pre-stage uniform analyst promises on the genuine volume-limit scalar.

Need verify limit assumptions via period-limit expansion and analytic estimates as in E (or otherwise!), in particular signed external equality and
one-step recurrence including generated future R.

Has no threshold γ!

Including θ-shaped derivative for non-silent pols etc. -/
def Patrons {P : Patch} {Z : Stage} (s : RG.Supply.Sheet G) (R T : PathData G) (p : Clip) (O : ChartRatio G) (Λ α:ℝ) :=
    ∀ (h : R.Bounds Z.clip Z.width Z.paths Λ) (c : Side) (x y : Site c) (σ τ : TypeFace 1→G.ColorIndex → ℂ),
    ∀ (_ : ∀ i j, ‖σ i j‖≤1) (_ : ∀ i j, ‖τ i j‖≤1), ∀ (_ : (atlas s P Z).serves c),
      let W := Inflation.lame (G:=G) x σ; let Y := Inflation.lame (G:=G) y τ
      (↑c.val:ℝ)^4 * (atlas s P Z).limit h O W Y = jet 2 (draft α T p) ![wave x σ,wave y τ]

section
variable {P} {Z}
-- Match with concrete step using the same actual normalization
lemma scopes (hs : S.kernel=s.kernel) (hP : S.patch=P) (h : R.Bounds Z.clip Z.width Z.paths Λ)
    (ht : Critical F Z.clip R ρ) (hO : LocalRatio O) (hq : Larger (G:=G) S) :
    let a := atlas s P Z
    Patrons (P:=P) (Z:=Z) s R T q O Λ α →
      a.allowance ≤ θ → γ ≤ a.sights →
      FreshDet (S:=S) F t R T Z.clip q ρ O α θ γ := by
  cases S with
  | mk p' t' hg =>
  dsimp only at hs hP; subst t'; subst p'; intro a h₁ h₂ h₃ i j k d hK hD
  have hm : a.bulletin hg := hq
  have ha : a.serves c := by
    have he : f=Paintings.canvas P c := Subtype.ext hg
    subst f; exact hm
  let u := wave (G:=G) i k; let v := wave (G:=G) j d
  let U := Inflation.lame (G:=G) i k; let V := Inflation.lame (G:=G) j d -- G inference
  let f₁ := a.billing hg hm R h O U V; let n := (c.val:ℝ)^4
  have he := h₁ h c i j k d hK hD ha; change n*a.limit h O U V = _ at he
  obtain ⟨hp,hB,hF⟩:= a.spent h hO ha U V (Inflation.score (G:=G) _ _ hK) (Inflation.score (G:=G) _ _ hD)
  let X := determinant (S:=stepped s.kernel hg) F t R Z.clip ρ O -- issue maybe S defeq
  have hx := @Dividends.authentically G c f (stepped _ hg) t F P.J Z.order Z.width Z.paths Λ Z.clip R s.kernel O a.h h hq rfl rfl a.enough hO ρ ht
  obtain ⟨-,-,hy,-⟩:=hx
  have hu : n*a.buys h O U V = (jet 2 X) ![u,v] := by
    have hg' := a.declaration h hO hg hm F t ρ ht U V
    have hz := hg'.trans (a.honest h ha hm O U V)
    have hb : 0<(c.val:ℝ) := by exact_mod_cast c.pos
    have hn : 0<n := pow_pos hb _
    rw [← hz,mul_comm, show (c.val:ℝ)^4=n from rfl,div_mul_cancel₀ _ hn.ne', Inflation.spectrum X u v hy]; rfl
  change |(jet 2 X) ![u,v] - _| ≤ _; rw [← he,← hu,← mul_sub,abs_mul, site_card]
  rw [abs_of_nonneg (by unfold n; positivity : 0≤n)]; push_cast
  have hh := Real.exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg h₃) (Nat.cast_nonneg c.val))
  calc
    _ ≤ n*(a.allowance*Real.exp (-a.sights * c.val)) := by unfold n; gcongr
    _ ≤ n*(θ*Real.exp (-γ*c.val)) := by apply mul_le_mul_of_nonneg_left (mul_le_mul h₂ hh (Real.exp_pos _).le (hB.trans h₂)); unfold n; positivity
    _ = _ := by unfold n; ring
end
end Solo

section Ledger
open RG.Supply Inherited

-- choose D already and Pre-purchase B eligible via this helper (may also
-- simultaneously lock requests for Rebuild.global advances at P.c/Γ --
-- not proved here, Γ possibly much too large/γ too small! Might then further
-- enlarge W,Y or need stronger loop prices than this post result.)
structure Works (B : Timing.Increments D) : Prop where
  above : pref D ≤ B.gamma
  legal : B.distance ≤ knot D




variable {a : Levels G} {Q : PostCost D} {W : Horizon a} {K : MapPrices} {U : Apertures} {A : ClassicalCosts} {H : QuantumCosts}
 {Θ : Protection D} {Y : Supply.Delays Θ} {X0 : Bar Y} {I : Wait X0} (ha : Paid I a)
variable {X : Issuer.Passport a} {N0 m : ℕ} {T : PathData G} {ρ : Branch a m} {O : ChartRatio G} (B : Timing.Increments D)

include ha
lemma paid (_h : m<N0) (ht : Issuer.Marking W K U A N0 (m+1) T)
    {F₀ : PathData G} {α : ℝ} (hP : LocalRatio O) (H₁ : Works B) (he : Q.Γ=B.gamma) (hr : Q.c=B.distance)
    (hh : OnShell W Q N0 m T ρ) (hv : Warm H Y) -- unbound H?
    (g : Patrons (P:=sheet s D (a.clock.adm (m+1))) (Z:=s.profile (a.clock.J (m+1))) s T F₀ (a.params m).clip O (a.clock.loopCap (m+1)) α) :
    ∀ p, ∃ T' t, let i:=a.clock.J (m+1); FreshDet (S:=a.clock.op m p) T' t T F₀ (a.params (m+1)).clip (a.params m).clip (ρ p T') O α (Q.Γ i) (Q.c i) := by
  intro p
  let S := a.clock.op m p
  let F := Classical.choice (Tree.select S.ratio S.patch.odd_side)
  let P := sheet s D (a.clock.adm (m+1)); let j:=a.clock.J (m+1); let V := atlas s P (s.profile j)
  have hs : S.patch=P := by
    have ht : S.patch.L=D.L j := block_eq ha m
    cases h0 : S.patch with
    | mk L0 j' Hj HL Hh =>
      have : j'=j := by rw [← show (@Patch.mk L0 j' Hj HL Hh).J=j' from rfl,← h0]; rfl
      have h : L0=D.L j :=  by rw [h0] at ht; exact ht
      subst j'; subst L0; rfl
  have hS : a.params (m+1) = s.profile j := congr_fun ha.stage _
  have hl : Larger (G:=G) S := larger hv ha ..
  let t' : S.Choices := Classical.arbitrary _
  have hb := ht.funded; have hK' := hh.critical p F; rw [hS] at hb hK'
  have hx : S.kernel=s.kernel := ha.kernel
  have hu := scopes F t' (α:=α) (θ:=Q.Γ j) (γ:=Q.c j) (T:=F₀) (q:=(a.params m).clip) hx hs hb hK' hP hl
  refine ⟨F,t',?_⟩
  rw [hS]
  apply hu g
  · apply le_trans _ (le_trans (H₁.above j) (by rw [he]))
    unfold pref; rw [dif_pos (a.clock.adm (m+1))]; exact le_max_right ..
  rw [hr]
  refine (H₁.legal j).trans (knot_low (a.clock.adm (m+1)) ?_)
  -- Vol positivity need any c with patched parameters. use hl.
  change 0<V.sights
  have hm : V.serves (a.S.side m p) := by
    have Hx := hl.2.1; have hX := hl.2.2; rw [hs] at Hx
    refine ⟨s.has _,?_,hX⟩
    rw [S.sizes,hs] at Hx -- larger size f, exact
    exact Hx
  have hs' := V.spent hb hP hm (0:Paintings.scale (a.S.side m p) G) 0 (by simp) (by simp)
  exact hs'.1
end Ledger
end YM.Further.PhysicalPeriodLimitF933.Mural
