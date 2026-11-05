import YM.Next.UV_STRESS.Oblique
import YM.Next.UV_STRESS.Rates


/-!
# Joining old and new at k in the phase approximation

Literal products on reflected h-placements. Expose *exact* physical moment
formula incl integration of all subsets/signs before budgeting (cancellations,
not packed absolute values at cutoff).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Function Set Filter MeasureTheory Analysis Extraction Table Ward Lattice Wilson Overlay Marker Cells RG
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (C : Family G)
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N p ℓ k h m : ℕ}

def chooseMode (t : Finset ι) : (Stock.census ι).Mode := ⟨t,Finset.mem_univ _⟩

private lemma back_linear {κ : Type*} (D : Finset κ) (g : κ → Config G (C.side k p) → ℂ) (r : κ→ℂ)
    (hp : ∀ i∈D, Envelope (g i)) (h : k≤m) (N) :
    stack C p N k m (fun x => ∑ i∈D, r i*g i x) h = fun x => ∑ i∈D,r i*stack C p N k m (g i) h x := by
  induction m,h using Nat.le_induction with
  | base => simp_rw [stack_origin]
  | succ m h ih =>
    rw [stack_step C _ _ _ _ _ h,ih]; simp_rw [stack_step C _ _ _ _ _ h]; funext x
    unfold back; simp_rw [Finset.smul_sum,← integral_const_mul]
    let β := C.path.β N p (m+1)
    have ht (y : Config G (C.side m p)) (i : κ) : (operation C p m).density β x y • (r i*stack C p N k m (g i) h y)= r i *
        ((operation C p m).density β x y • stack C p N k m (g i) h y) := by simp only [Complex.real_smul]; ring
    dsimp only [β] at ht; simp_rw [ht]; exact integral_finsetSum D fun i hi => ((pull_int _ (stack_envelope C _ _ _ _ (g i) h (hp i hi))
      (step_approved C p m) _ x)).const_mul _

omit [Fintype ι] [DecidableEq ι] in
private lemma shelf_cost {α} [MeasurableSpace α] {w : ι → α → ℂ} (hu : ∀ i,Envelope (w i)) (s : Finset ι) :
    Envelope (fun x => ∏ i∈s,w i x) := by
  constructor
  · exact Finset.measurable_fun_prod _ fun i _ => (hu i).meas
  choose c hc using fun i => (hu i).cost
  -- empty domain cost works too; mul only when x supplied
  exact ⟨∏ i∈s,c i,fun x => by simp only [norm_prod]; exact Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hc i x⟩

variable (L : Overlay.Lane C.path (Stock.census ι) N p)

def acquire (s : Finset ι) (g : ι → Config G (C.side k p) → ℂ) (U) (V : Config G (C.side k p)) :=
    ∏ i∈s,(g i V-L.uses i U)

def qualified (s : (Stock.census ι).Mode) (h : k ≤ N) (Y : ι → Config G (C.side k p) → ℂ) : Config G (C.side N p)→ℂ :=
    fun U => stack C p N k N (acquire C L s.val Y U) h U

/-- Every subset, this is after old multipoint insertion *and* restriction
by signed summation. The spectrum here on the left/right is the actual scalar
paths in the same trajectory. -/
def consume (g : ι → Config G (C.side k p) → ℂ) (s : (Stock.census ι).Mode) (V : Config G (C.side k p)) :=
    ∑ q∈s.val.powerset, (-1:ℂ)^q.card * (Ride.bump (C.S.a k) (chooseMode (s.val\q)) L.load *
      ∏ i∈s.val\q,g i V) * L.signal k (chooseMode q) V

private def shelved (g : ι → Config G (C.side k p) → ℂ) (s : Finset ι) (x : Config G (C.side k p)) := ∏ i∈s, g i x
private lemma prices (Q s : Finset ι) (h : Q ⊆ s) : Ride.bump (C.S.a k) (chooseMode (s\Q)) L.load *
    Ride.bump (C.S.a k) (chooseMode Q) L.load= Ride.bump (C.S.a k) (chooseMode s) L.load := by
  rw [mul_comm]; unfold Ride.bump; dsimp only [chooseMode]
  rw [← Finset.prod_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset h]

lemma acquire_all (s : Finset ι) (g : ι → Config G (C.side k p) → ℂ) (h : k ≤ N) (u)
    (hh : ∀ i, Envelope (g i)) :
    stack C p N k N (acquire C L s g u) h u =
      ∑ q∈s.powerset, (-1:ℂ)^q.card * (stack C p N k N (shelved C g (s\q)) h u * Ride.Product L.uses (chooseMode q) u) := by
  let B (q : Finset ι) := (-1:ℂ)^q.card * Ride.Product L.uses (chooseMode q) u
  let G₁ (q : Finset ι) := shelved C g (s\q)
  have he : acquire C L s g u = fun V => ∑ q∈s.powerset, B q*G₁ q V := by
    funext V; unfold acquire; simp only [sub_eq_add_neg]; simp_rw [add_comm (g _ _), Finset.prod_add]
    apply Finset.sum_congr rfl; intro i _; unfold G₁ shelved B Ride.Product; rw [Finset.prod_neg]; rfl
  rw [he, back_linear C _ G₁ B (fun i _ => shelf_cost hh _) h]
  apply Finset.sum_congr rfl; intro i _; unfold B G₁; ring

private lemma shelf_test (h : L.Works k) (s u : Finset ι) (g : ι → Config G (C.side k p)→ℂ) (ht : ∀ i,Envelope (g i)) :
    Integrable (fun x => (-1:ℂ)^s.card * (stack C p N k N (shelved C g u) h.admits x * Ride.Product L.uses (chooseMode s) x))
      (law G _ (C.beta N p)) := by
  have he := stack_envelope C p N k N (shelved C g u) h.admits (shelf_cost ht _)
  have ht : Integrable (Ride.Product L.uses (chooseMode s)) (law G (C.side N p) (C.beta N p)) := h.reads (chooseMode s)
  exact (final_mul (law G _ (C.beta N p)) (stack C p N k N (shelved C g u) h.admits) (Ride.Product L.uses (chooseMode s)) he ht).const_mul _

lemma serves_moments (P : C.Makes) (h : L.Works k) (s : (Stock.census ι).Mode) (g : ι → Config G (C.side k p) → ℂ)
    (hp : ∀ i, Envelope (g i)) : Integrable (qualified C L s h.admits g) (law G _ (C.beta N p)) ∧
      (∫ V, consume C L g s V ∂prior G _)=Ride.bump (C.S.a k) s L.load * (partition G (C.side N p) (C.beta N p):ℂ) *
        moment (C.beta N p) (qualified C L s h.admits g) := by
  let t := s.val.powerset
  let x := s.val
  let Q (u : Finset ι) := shelved C g (x\u)
  let A (u : Finset ι) V := stack C p N k N (Q u) h.admits V * Ride.Product L.uses (chooseMode u) V
  have hv (u : Finset ι) : Envelope (Q u) := shelf_cost hp _
  have he : qualified C L s h.admits g = fun V => ∑ u∈t, (-1:ℂ)^u.card * A u V := funext fun _ => acquire_all C L _ _ _ _ hp
  rw [he]; refine ⟨integrable_finsetSum _ fun i _ => shelf_test C L h i _ _ hp,?_⟩
  let v (u : Finset ι) := Q u * L.signal k (chooseMode u)
  let b (u : Finset ι) := Ride.bump (C.S.a k) (chooseMode (x\u)) L.load
  rw [show consume C L g s= fun V => ∑ u∈t, ((-1:ℂ)^u.card * b u) * v u V from ?_, moment, integral_finsetSum,integral_finsetSum,
    Finset.mul_sum]
  · apply Finset.sum_congr rfl; intro i hi
    rw [integral_const_mul, integral_const_mul]
    have hp : chooseMode s.val=s := rfl
    have he := prices (k:=k) C L i s.val (Finset.mem_powerset.mp hi); rw [hp] at he
    have hz := basis_jump C L h P (Q i) (hv i) le_rfl h.admits (chooseMode i)
    simp_rw [stack_origin] at hz
    rw [show ∫ V, v i V ∂prior G _=_ from hz, ← he]; unfold b x moment A; ring
  · exact fun i _ => shelf_test C L h i _ _ hp
  · rintro i hi
    obtain ⟨hh,w,l,c,d,e,hv'⟩ := h.meaningful _ le_rfl h.admits
    have ht := ((L.sites k).material hh hv' (P.wilson.represents N p k h.admits).good
      (beta_positive P.wilson h.admits).le (chooseMode i)).1
    exact (show Integrable (v i) (prior G _) from ht.bdd_smul (hv i).cost.choose
      (hv i).meas.aestronglyMeasurable (Eventually.of_forall (hv i).cost.choose_spec)).const_mul _
  funext V; apply Finset.sum_congr rfl; intro i _; unfold v Q x b shelved; rw [Pi.mul_apply]; ring
end YM.Next.UVStress
