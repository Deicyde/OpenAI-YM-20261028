import YM.RG08.Gaussian.Turning
import YM.RG08.Flat.KLimit

/-! # Pre-block Gaussian ledger on the Wilson Chain -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Function Filter Lattice Wilson RG Precision Exterior Bloch Matrix Laurent
open Next.Free Work.F08 Tree Stationary
open scoped Topology BigOperators Classical

variable {G : Gauge} {X : Chain}
namespace Chain

def trees (X : Chain) (i : ℕ) := Repeated.axisRule (X.patch i).L (X.patch i).odd_side

def Wake (G : Gauge) (X : Chain) := ∀ i,(X.patch i).Branches X.kernel G
lemma wake_actual (a : Levels G) : Wake G (actual a) := fun i => (a.blocks i 0).branches

-- p implicit for some joins; set patch type fixed here

def curve (G : Gauge) (X : Chain) (N i : ℕ) := conditionalCov G (P:=X.patch i)
    (X.trees i) X.kernel (X.history N (i+1))

def predict (G : Gauge) (X : Chain) (N i : ℕ) := coarseMean G (P:=X.patch i)
    (X.trees i) X.kernel (X.history N (i+1))
lemma predict_truth (G : Gauge) (h : Wake G X) (N i : ℕ) (hp : i<N) (c f : Side)
    (ht : f.val=c.val*(X.S.block i).val) :
    let S:=X.pair i c f ht; let F := (X.trees i).forest S.ratio
    installed S.ratio (predict G X N i)=patron G (extracted S F (installed S.ratio (X.A₀ N i))) := by
  intro S F
  have hv : (predict G X N i).acts c=repackM (unitSplit G S 1) (Equiv.refl _) (patron G (extracted S F (installed S.ratio (X.A₀ N i)))) :=
    ((slice_compute (P:=X.patch i) (k:=X.kernel) (X.trees i) (X.history N (i+1)) (h _) c f ht).2.2.2.2 _ _
      (X.canonical _ _ hp ht))
  ext x y
  rw [installed, Matrix.submatrix_apply]; erw [hv]
  simp only [repackM,id_eq,Matrix.submatrix_apply,Equiv.refl_symm,Equiv.refl_apply,unitSplit,Equiv.symm_apply_apply]
end Chain

lemma strip_flip {α β : Type} {A B : Row α β} {s C : ℝ} (h : (A-B).strip s C) :
    (B-A).strip s C := by
  intro i j; simpa only [Width,Pi.sub_apply,norm_sub_rev] using h i j

/-- Post prices at these *pre* widths. Caller to choose extra decreases,
    ensure block lower thresholds for σ crossing from K history.
    Coarse-width indexing. -/
structure Lending (G : Gauge) (K : KernelChoices) where
  w : ℕ→ℝ
  wpos : ∀ i, 0 < w i
  bill : ℕ→Patch→ℝ
  solvent : ∀ i p, 0≤bill i p
  serves (i : ℕ) (P : Patch) (ha : i=P.J ∨ i+1=P.J) (hP : P.Branches K G)
    (u v : Train P.J) :
    let X := Repeated.axisRule P.L P.odd_side
    let C := bill i P; let σ := w i
    (conditionalCov G (P:=P) X K u).strip σ C ∧ (coarseMean G X K u).strip σ C ∧
    ∀ η B : ℝ, 0≤B → σ≤P.L.val*η →
      (hessian (pink K.penalty u)-hessian (pink K.penalty v)).strip η B →
        (conditionalCov G X K u-conditionalCov G X K v).strip σ (C*B) ∧
        (coarseMean G X K u-coarseMean G X K v).strip σ (C*B)

lemma lenders (G : Gauge) (K : KernelChoices) : Nonempty (Lending G K) := by
  have hr (j : ℕ) : ∃ σ : ℝ, 0<σ ∧ ∀ (P : Patch), P.J=j → P.Branches K G →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ w : Train P.J,
        (conditionalCov G (P:=P) (Repeated.axisRule P.L P.odd_side) K w).strip σ M := by
    by_cases h : 4 ≤ j
    · obtain ⟨b,hb,H⟩ := conditional_funds G K j h
      exact ⟨b,hb,fun p hj hh => H p hj hh _⟩
    exact ⟨1,one_pos,fun P hp _ => (h (P.order_cut.trans_eq hp)).elim⟩
  choose b hb H using hr
  let w (j) := min (b j) (b (j+1))
  have hw j : 0<w j := lt_min (hb j) (hb (j+1))
  have hg (i : ℕ) (P : Patch) :
      let X := Repeated.axisRule P.L P.odd_side
      let σ := w i
      ∃ C : ℝ, 0≤C ∧ ((i=P.J ∨ i+1=P.J) → P.Branches K G → ∀ u v : Train P.J,
        (conditionalCov G (P:=P) X K u).strip σ C ∧ (coarseMean G X K u).strip σ C ∧
        ∀ η B : ℝ, 0≤B → σ≤P.L.val*η →
          (hessian (pink K.penalty u)-hessian (pink K.penalty v)).strip η B →
          (conditionalCov G X K u-conditionalCov G X K v).strip σ (C*B) ∧
          (coarseMean G X K u-coarseMean G X K v).strip σ (C*B)) := by
    intro X σ
    have hs : 0<σ := hw i
    by_cases hX : (i=P.J ∨ i+1=P.J) ∧ P.Branches K G
    · obtain ⟨D,hD,Hd⟩ := H P.J P rfl hX.2
      obtain ⟨M,hM,Hm⟩ := probe_budget G P K σ hs
      let n := (Fintype.card (Co P.L (Loc G 1)):ℝ)
      let E:= n*n*D*Real.exp (4*σ)*D
      let V:= ‖K.penalty‖*n*M
      have he : 0≤E := by unfold E n; positivity
      have hv : 0≤V := by unfold V n; positivity
      let C:= max (max D (V*D)) (max E (V*E))
      have hG (u) : (conditionalCov G X K u).strip σ D :=
        strip_mono (Hd u) (by
          rcases hX.1 with hl|hl <;> rw [← hl]; exact min_le_left ..; exact min_le_right ..) le_rfl
      have h₁ : V*D≤C := le_trans (le_max_right ..) (le_max_left ..)
      have h₂ : D ≤ C := le_trans (le_max_left ..) (le_max_left ..)
      refine ⟨C,hD.trans h₂,fun _ hK u v => ⟨strip_mono (hG _) le_rfl h₂, ?_,fun η B hp ht h => ?_⟩⟩
      · apply strip_mono (mean_budget _ _ _ (hG _) Hm hs.le) le_rfl; refine le_trans (le_of_eq ?_) h₁
        unfold V n; ring
      have hhV : (minusRows (conditionalCov G X K u) (conditionalCov G X K v)).strip σ (E*B) := by
        refine strip_mono (covariance_moves X hK (hG _) (hG _) (σ:=η) (C:=B) (strip_flip (α:=TypeFace 1) h) hs ht) le_rfl (le_of_eq ?_)
        unfold E n; ring
      constructor
      · exact strip_mono hhV le_rfl (mul_le_mul_of_nonneg_right ((le_max_left ..).trans (le_max_right ..)) hp)
      apply strip_mono (coarseMean_movement X hhV Hm hs) le_rfl
      apply Eq.trans_le _ (mul_le_mul_of_nonneg_right (show V*E≤C from (le_max_right ..).trans (le_max_right ..)) hp)
      unfold V n; ring
    exact ⟨0,le_rfl, fun hp hB => (hX ⟨hp,hB⟩).elim⟩
  dsimp only at hg
  choose v hv hh using hg
  exact ⟨⟨w,hw,v,hv,fun j P => hh j P⟩⟩

variable (K : KernelChoices)

lemma crossing {K : KernelChoices} {P : KPrices K} (g : KGate P) (Y : Lending G K) :
    ∃ b : ℕ→ℕ, ∀ i j, j=i ∨ j+1=i → ∀ L : Side, b i ≤ L.val → Y.w j≤L.val*g.w i := by
  choose h hh using fun i j : ℕ => exists_nat_gt (Y.w j/g.w i)
  refine ⟨fun i => max (h i i) (h i (i-1)),fun i j hj L hp => (div_le_iff₀ (g.pos _)).mp ?_⟩
  apply le_trans (hh i j).le
  rcases hj with hx|hx <;> subst i
  · exact_mod_cast ((le_max_left ..).trans hp : h j j≤L.val)
  dsimp only at hp; rw [Nat.add_sub_cancel] at hp
  exact_mod_cast ((le_max_right ..).trans hp : h (j+1) j≤L.val)

/-- `Wake` is patch branches for the gauge; exact specialization to any
 actual Levels. Stipulate the widths before imposing sized stage gates. -/
structure Clear (P : KPrices X.kernel) (g : KGate P) (Y : Lending G X.kernel) (ℓ : ℕ) : Prop where
  booked : KAllowed g ℓ
  large i : ℓ ≤ i → Y.w (X.J i) ≤ (X.S.block i).val * g.w (X.J (i+1))
  trueStep : X.Wake G

open Chain

lemma report_funding {G : Gauge} (X : Chain) (h : X.Wake G) (Y : Lending G X.kernel)
    (i : ℕ) (N : ℕ) :
    (curve G X N i).strip (Y.w (X.J i)) (Y.bill (X.J i) (X.patch i)) ∧
    (predict G X N i).strip (Y.w (X.J i)) (Y.bill (X.J i) (X.patch i)) := by
  have he : X.J i=(X.patch i).J ∨ X.J i+1=(X.patch i).J := by
    change X.J i=X.J (i+1) ∨ X.J i+1=X.J (i+1); have h := X.mono i; have hp := X.slow i; omega
  have hv := Y.serves _ _ he (h i) (X.history N (i+1)) (X.history N (i+1))
  exact ⟨hv.1,hv.2.1⟩

theorem overlap (A B : ℝ) (ha : 0≤A) (hb : 0≤B) (p q : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (G : Gauge) (X : Chain) (P : KPrices X.kernel) (g : KGate P)
      (Y : Lending G X.kernel) (k ℓ : ℕ) (Z : ℝ), 0≤Z →
      Clear P g Y ℓ →
        (let a := age X.S Z k
         (∀ i, ℓ ≤ i → P.bill (X.J i) ≤ A*a i^p) →
          (∀ i, ℓ ≤ i → Y.bill (X.J i) (X.patch i) ≤ B*a (i+1)^q) →
          ∀ i N N', ℓ ≤ i → i<N → N≤N' →
            let C:= c*a (i+1)^(p+q)*gain X.S (1/4) (i+1) N
            (curve G X N i-curve G X N' i).strip (Y.w (X.J i)) C ∧
            (predict G X N i-predict G X N' i).strip (Y.w (X.J i)) C) := by
  obtain ⟨D,hD,H⟩ := k_cauchy A ha p; refine ⟨B*D,mul_nonneg hb hD,?_⟩
  intro G X P g Y k ℓ Z hz hc a hf hF i N N' he hp hN C
  let b := D*a (i+1)^p*gain X.S (1/4) (i+1) N
  have hr : 1 ≤ a (i+1) := age_one (S:=X.S) hz k _
  have hb : 0 ≤ b := by unfold b; have hx:=gain_pos X.S (1/4) (i+1) N; positivity
  have hh : (X.K₀ N (i+1)-X.K₀ N' (i+1)).strip (g.w (X.J (i+1))) b := H _ _ _ Z hz ℓ k hc.booked hf _ _ _ (he.trans (Nat.le_succ _)) hp hN
  have hw : X.J i=(X.patch i).J ∨ X.J i+1=(X.patch i).J := by
    change X.J i=X.J (i+1) ∨ X.J i+1=X.J (i+1); have h := X.mono i; have hp := X.slow i; omega
  have ht := (Y.serves _ _ hw (hc.trueStep i) (X.history N (i+1)) (X.history N' (i+1))).2.2 _ _ hb (hc.large i he) hh
  have hy : (Y.bill _ _) * b≤ C := (mul_le_mul_of_nonneg_right (hF i he) hb).trans_eq (by unfold C b; rw [pow_add]; ring)
  exact ⟨strip_mono ht.1 le_rfl hy, strip_mono ht.2 le_rfl hy⟩
end YM.RG08
