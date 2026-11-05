import YM.Next.UV_STRESS.Shell

/-!
# Both unnormalized local Ward charges, as actual field maps
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Filter Function Set MeasureTheory Analysis Extraction Table Ward Climb Work.A01
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {L : Register G} {T : Table L} {n d D : ℕ}

/-- Dependence on the complex label at the center. -/
def chargeField (H : T.Smooth) (J : T.Stress) {χ : E4 → ℝ} (x : Points (n+1)) (hx : x ∈ conf _)
    (h : Window x χ) (V : E4 → E4) (hv : ∀ i : Axis,Continuous (fun y => V y i)) (q : Fin n → T.Tag) (d : ℕ) :
    T.Field d →ₗ[ℂ] ℂ where
  toFun := flux J χ V x q
  map_add' A B := by
    have ht (v : T.Field d) (i j) := term_integrable J χ V x q v H hx h i j (hv j)
    have he i j y : term J χ V x q (A+B) i j y = term J χ V x q A i j y + term J χ V x q B i j y := by
      by_cases hz : Analysis.D (basis i) χ y=0
      · simp [term,hz]
      unfold term; simp_rw [← mul_add]
      let p : Fin (n+2) → T.Tag := Fin.cons ⟨4,J i j⟩ (Fin.cons ⟨d,A⟩ q)
      let F := here p (Points.cons y x) (0 : Fin (n+1)).succ d
      have hh (v) : F v=T.useAt T (Points.cons y x) (Fin.cons ⟨4,J i j⟩ (Fin.cons ⟨d,v⟩ q)) := by
        unfold F; rw [takes]; simp only [p, ← Fin.cons_update, Fin.update_cons_zero, disc]
      rw [← hh,← hh,← hh,map_add]
    simp_rw [flux,he,integral_add (ht _ ..) (ht _ ..),Finset.sum_add_distrib,neg_add]
  map_smul' c A := by
    have he i j y : term J χ V x q (c • A) i j y = c • term J χ V x q A i j y := by
      let p : Fin (n+2) → T.Tag := Fin.cons ⟨4,J i j⟩ (Fin.cons ⟨d,A⟩ q)
      let F := here p (Points.cons y x) (0 : Fin (n+1)).succ d
      have hh (v) : F v=T.useAt T (Points.cons y x) (Fin.cons ⟨4,J i j⟩ (Fin.cons ⟨d,v⟩ q)) := by
        unfold F; rw [takes]; simp only [p, ← Fin.cons_update, Fin.update_cons_zero, disc]
      unfold term; rw [← hh,← hh,map_smul,smul_eq_mul,smul_eq_mul]; ring
    simp_rw [flux,he,integral_smul, ← Finset.smul_sum, ← smul_neg]; rfl

def chargeAngular (H : T.Smooth) (J : T.Stress) {χ : E4 → ℝ} (x : Points (n+1)) (hx : x ∈ conf _)
    (h : Window x χ) (q : Fin n → T.Tag) (v : T.Field d) : Ortho.Skew →ₗ[ℝ] ℂ where
  toFun k := flux J χ (orbital k (x 0)) x q v
  map_add' A B := by
    have ht k i j := term_integrable J χ (orbital k (x 0)) x q v H hx h i j (smooth_orbital k _ j).continuous
    have he (i j : Axis) (y) : term J χ (orbital (A+B) (x 0)) x q v i j y =
        term J χ (orbital A (x 0)) x q v i j y + term J χ (orbital B (x 0)) x q v i j y := by
      have hh : orbital (A+B) (x 0) y j=orbital A (x 0) y j+ orbital B (x 0) y j := by
        simp [orbital, M4.at_coord,add_mul, Finset.sum_add_distrib]
      unfold term; rw [hh]; push_cast; ring
    simp_rw [flux, he, integral_add (ht ..) (ht ..), Finset.sum_add_distrib, neg_add]
  map_smul' c A := by
    rw [show orbital (c • A) (x 0) = (fun y => c • orbital A (x 0) y) from ?_,flux_scale]
    · exact Complex.real_smul.symm
    funext y; ext1 i; simp [orbital,M4.at_coord,mul_assoc,Finset.mul_sum]

variable {C : Family G} {S : Table C.book} {F : Extraction.Order} {V : DiffPlan S}

private lemma map_shell (v : S.Field d → S.Field D) (h : S.Hierarchy) (J : S.Stress) (U : E4 → E4)
    (hu : ∀ i : Axis,Continuous (fun y => U y i)) (hp : ∀ B (n : ℕ) (q : Fin n→S.Tag) (x : Points (n+1)), x∈conf _ →
      ∀ χ, Window x χ → flux J χ (fun y => U (y - x 0)) x q B = disc (Fin.cons ⟨D,v B⟩ q) x) :
    ∃ M : S.Field d →ₗ[ℂ] S.Field D, ∀ B,M B=v B := by
  have he (B) (n) (q : Fin n→S.Tag) (x) (ht : x∈conf (n+1)) (χ) (hw : Window x χ)
      (ho : ∀ i : Axis,Continuous (fun y => U (y-x 0) i)) :
      frontRead q x D (v B)=chargeField h.smooth J x ht hw (fun y => U (y-x 0)) ho q d B :=
    (front_eval ..).trans (hp B n q x ht χ hw).symm
  have hU (t : E4) (i : Axis) : Continuous (fun y => U (y-t) i) := (hu i).comp (continuous_id.sub continuous_const)
  refine ⟨⟨⟨v,?_⟩,?_⟩,fun B => rfl⟩
  · intro B D'; apply S.field_ext h.laws.toSymmetric
    intro n q x hx
    obtain ⟨χ,hχ⟩ := exists_window x hx
    simp_rw [← front_eval,map_add]; rw [he _ _ _ _ hx χ hχ (hU (x 0)), he _ _ _ _ hx χ hχ (hU (x 0)),
      he _ _ _ _ hx χ hχ (hU (x 0)), map_add]
  intro c B; change v (c • B) = c • v B
  apply S.field_ext h.laws.toSymmetric; intro n q x hx
  obtain ⟨χ,hχ⟩ := exists_window x hx
  simp_rw [← front_eval,map_smul]; rw [he _ _ _ _ hx χ hχ (hU (x 0)), he _ _ _ _ hx χ hχ (hU (x 0)),map_smul]

lemma shells_operate (hC : C.Makes) (hs : Cells.CellHyp C F) (ho : F.PointLimits C S)
    (H : S.Hierarchy) (h : V.Derivatives S) (J : S.Stress) (hc : Conserved V H.spin J)
    (ht : Probed F J) :
    ∃ (p : Parts S) (Y : SpinRows S), StressLaws S J p Y := by
  choose X hX using fun d (i : Axis) v => annular_field hC hs ho H h hc (d:=d) v (fun _ => basis i) (fun _ => contDiff_const)
    (killing_const _) 0 (fun _ _ _ => by simp) (d+1) (ht.tr d v)
  choose P hP using fun d i => map_shell (X d i) H J (fun _ => basis i) (fun _ => continuous_const) (hX d i)
  have hv (k : Ortho.Skew) (y : E4) (r : ℝ) : orbital k 0 (r • y)= r^1 • orbital k 0 y := by
    simp only [orbital,M4.move,sub_zero,map_smul,pow_one]
  choose Y hY using fun d k v => annular_field hC hs ho H h hc (d:=d) v (orbital k 0)
    (smooth_orbital k 0) (killing_orbital k 0) 1 (fun y r _ => hv k y r) d (ht.ro d v)
  choose R hR using fun d k => map_shell (Y d k) H J (orbital k 0) (fun i => (smooth_orbital k 0 i).continuous) (hY d k)
  have hu {n} q k d B (x : Points (n+1)) (hx : x∈conf _) χ (hw : Window x χ) :
      frontRead q x d (R d k B)=chargeAngular H.smooth J x hx hw q B k := by
    rw [front_eval,hR]; exact (by
      simpa [orbital] using! (hY d k B n q x hx χ hw).symm)
  let T : SpinRows S := fun d => { toFun := R d
                                   map_add' := ?_, map_smul' := ?_ }
  · refine ⟨P,T,fun {n} {x} hx q {χ} w b d B => ?_,fun {n} {x} hx q {χ} w k d B => ?_⟩
    · rw [← flux_translation,hP]; exact hX d b B n q x hx _ w
    rw [← flux_spin,← front_eval]; exact (hu q k d B x hx _ w).symm
  · intro a b; apply LinearMap.ext; intro v
    apply S.field_ext H.laws.toSymmetric; intro n q x hx
    obtain ⟨χ,hχ⟩ := exists_window x hx
    change S.useAt S _ _ = S.useAt S x (Fin.cons ⟨d,R d a v+R d b v⟩ q)
    rw [← front_eval,← front_eval,map_add]; simp only [hu _ _ _ _ _ hx χ hχ,map_add]
  intro r k; apply LinearMap.ext; intro v; apply S.field_ext H.laws.toSymmetric; intro n q x hx
  obtain ⟨χ,hχ⟩ := exists_window x hx
  change S.useAt S _ _ = S.useAt S x (Fin.cons ⟨d,r • R d k v⟩ q)
  rw [← front_eval,← front_eval, show frontRead q x d (r • R d k v)=r • frontRead q x d (R d k v) from
    ((frontRead q x d).restrictScalars ℝ).map_smul .., hu q k d v _ hx χ hχ, hu q (r • k) d v _ hx χ hχ,map_smul]
end YM.Next.UVStress
