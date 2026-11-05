import YM.WilsonBulk.Web.Accounts

/-!
# Operations composing rooted, connected (bulk) coefficients

`seam` has one shared vertex (including any type-coordinate in its alphabet).
`pluck` is used only with nonempty remaining legs on the cover, so never a
volume sum in the vacuum recursion. A weighted loop may additionally need a
pointwise product estimate but not a second width penalty. Strict-event lifts
will insert Γ using these operations on mixed cells. Utilities also encode
simple accuracy comparisons.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Topology Classical BigOperators ENNReal
open Function Lattice Pert.Bulk
variable {X Y α β : Type} {σ θ p q : ℝ} {k n m : ℕ} {D : Rule X}

def pluck (u : Page X (n+1)) : Page X n := fun v => ∑' x, u (hitch x v)
def seam (a : Page X (k+1)) (b : Page X (n+1)) : Page X ((k+n)+1) :=
    fun v => a (hitch (v 0) (snip k n (crop v))) * b (hitch (v 0) (keep k n (crop v)))
lemma seam_apply (a : Page X (k+1)) (b : Page X (n+1)) (x : X) (u : Legs X k) (v : Legs X n) :
    seam a b (hitch x (Fin.append u v)) = a (hitch x u)*b (hitch x v) := by simp [seam]

variable {a a' : Page X (k+1)} {b b' : Page X (n+1)}

lemma Within.plucked (h : Within D σ p b) (hσ : 0 ≤ σ) : Within D σ p (pluck b) := by
  refine ⟨h.1,fun i x=>?_⟩
  apply LE.le.trans ?_ (h.2 i.succ x); rw [rent_tail, ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum fun v=>?_
  by_cases he : v i=x; swap; · simp [he]
  simp only [he,↓reduceIte]; apply (bill_tsum ..).trans (ENNReal.tsum_le_tsum fun y=>?_)
  exact bill_mono le_rfl (mul_le_mul_of_nonneg_left ((le_add_of_nonneg_left (D.nonneg x y)).trans_eq (run_some ..).symm) hσ)
-- summability for use in nonextensive operations
lemma Within.over_pluck (h : Within D σ p b) (hσ : 0 ≤ σ) (hn : n ≠ 0) (v : Legs X n) :
    Summable fun x => b (hitch x v) := by
  let j : Fin n := ⟨0,by omega⟩
  have H := within_total h hσ j.succ (v j)
  let f (x : X) := hitch x v
  have h' : Injective f := fun a b e=>congr_fun e 0
  apply (H.comp_injective h').congr
  intro x; simp [f]

@[simp] lemma pluck_zero : pluck (0:Page X (n+1))=0 := by simp [pluck, funext_iff]
lemma pluck_scale (r : ℝ) : pluck (r • b)=r • pluck b := by funext x; simp [pluck,tsum_mul_left]
lemma pluck_add (h : Within D σ p b) (h' : Within D θ q b') (hp : 0≤σ) (hq : 0≤θ) (hn : n ≠ 0) :
    pluck (b+b') = pluck b+pluck b' := funext fun v=> (h.over_pluck hp hn v).tsum_add (h'.over_pluck hq hn v)
lemma pluck_sub (h : Within D σ p b) (h' : Within D θ q b') (hp : 0≤σ) (hq : 0≤θ) (hn : n ≠ 0) :
    pluck (b-b') = pluck b-pluck b' := funext fun v=> (h.over_pluck hp hn v).tsum_sub (h'.over_pluck hq hn v)

lemma rent_seam_root (ha : Within D σ p a) (hb : Within D σ q b) (x : X) :
    rent D σ (seam a b) 0 x ≤ ENNReal.ofReal (p*q) := by
  have he := ha.2 0 x; have hh := hb.2 0 x
  rw [rent_head] at he hh ⊢; rw [ts_plus]
  simp_rw [seam_apply,run_joint,mul_add,purchase,ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, ENNReal.ofReal_mul ha.1]
  exact mul_le_mul' he hh

lemma run_across (hp : 0≤θ) (he : ((n:ℝ)+1)*θ ≤ σ) (x y : X) (u : Legs X k) (v : Legs X n) :
    θ*(D.cost x y+run D x u+run D x v) ≤ σ*run D x (hitch y u)+θ*run D y v := by
  rw [run_some]
  calc _ ≤ θ*(D.cost x y+run D x u+ (n*D.cost x y+ run D y v)) := mul_le_mul_of_nonneg_left (by gcongr; exact run_move ..) hp
       _ ≤ ((n:ℝ)+1)*θ*(D.cost x y+run D x u)+θ*run D y v := by
            nlinarith only [mul_nonneg (Nat.cast_nonneg n) (mul_nonneg hp (run_nonneg D x u))]
       _ ≤ _ := by gcongr; exact add_nonneg (D.nonneg ..) (run_nonneg ..)

lemma purchase_across (hp : 0 ≤ θ) (he : ((n:ℝ)+1)*θ ≤ σ) (a b : ℝ)
    (x y : X) (u : Legs X k) (v : Legs X n) : bill (a*b) (θ*(D.cost x y+run D x u+run D x v)) ≤
    bill a (σ*run D x (hitch y u))*bill b (θ*run D y v) := bill_mul _ _ _ _ _ (run_across hp he ..)

lemma rent_seam_left (ha : Within D σ p a) (hb : Within D θ q b) (hp : 0≤θ) (he : ((n:ℝ)+1)*θ ≤ σ) (i : Fin k) (x : X) :
    rent D θ (seam a b) (Fin.castAdd n i).succ x ≤ ENNReal.ofReal (p*q) := by
  rw [rent_tail, ENNReal.ofReal_mul ha.1]
  have hx := mul_le_mul_left (ha.2 i.succ x) (ENNReal.ofReal q)
  rw [rent_tail] at hx
  simp_rw [← ENNReal.tsum_mul_right] at hx
  refine LE.le.trans (ENNReal.tsum_le_tsum (fun y=>?_)) hx
  rw [ts_plus]; refine ENNReal.tsum_le_tsum fun u=>?_
  simp only [Fin.append_left]; split_ifs with hk; swap; · simp
  have ht := mul_le_mul_right (hb.2 0 y) (bill (a (hitch y u)) (σ*run D x (hitch y u)))
  rw [rent_head, ← ENNReal.tsum_mul_left] at ht
  refine LE.le.trans (ENNReal.tsum_le_tsum fun v=>?_) ht
  rw [seam_apply,run_some,run_joint,← add_assoc]
  exact purchase_across hp he (a (hitch y u)) (b (hitch y v)) ..

lemma rent_seam_right (ha : Within D θ p a) (hb : Within D σ q b) (hp : 0≤θ) (he : ((k:ℝ)+1)*θ ≤ σ) (i : Fin n) (x : X) :
    rent D θ (seam a b) (Fin.natAdd k i).succ x ≤ ENNReal.ofReal (p*q) := by
  rw [rent_tail,ENNReal.ofReal_mul ha.1]
  have hx := mul_le_mul_right (hb.2 i.succ x) (ENNReal.ofReal p)
  rw [rent_tail] at hx
  simp_rw [← ENNReal.tsum_mul_left] at hx
  refine LE.le.trans (ENNReal.tsum_le_tsum (fun y=>?_)) hx
  rw [ts_plus, ENNReal.tsum_comm]; refine ENNReal.tsum_le_tsum fun u=>?_
  simp only [Fin.append_right]; split_ifs with hk; swap; · simp
  have ht := mul_le_mul_left (ha.2 0 y) (bill (b (hitch y u)) (σ*run D x (hitch y u)))
  rw [rent_head, ← ENNReal.tsum_mul_right] at ht
  refine LE.le.trans (ENNReal.tsum_le_tsum fun v=>?_) ht
  rw [seam_apply, run_some, run_joint, add_comm (run D x v), ← add_assoc, mul_comm (a _), mul_comm (bill (a _) _)]
  exact purchase_across hp he (b (hitch y u)) (a (hitch y v)) ..

lemma Within.sewn (ha : Within D σ p a) (hb : Within D σ q b) (hp : 0≤θ) (he : ((n:ℝ)+1)*θ ≤ σ) (hh : ((k:ℝ)+1)*θ ≤ σ) :
    Within D θ (p*q) (seam a b) := by
  have hs : θ ≤ σ := (le_mul_of_one_le_left hp (by norm_cast; omega)).trans he
  have h₁ := ha.mono hs le_rfl; have h₂ := hb.mono hs le_rfl
  refine ⟨mul_nonneg ha.1 hb.1,fun j x=> Fin.cases (rent_seam_root h₁ h₂ x) (fun i=>?_) j⟩
  exact Fin.addCases (fun v=> rent_seam_left ha h₂ hp he v x) (fun v=> rent_seam_right h₁ hb hp hh v x) i

@[simp] lemma seam_zero_left (a : Page X (n+1)) : seam (0:Page X (k+1)) a=0 := by ext1 x; simp [seam]
@[simp] lemma seam_zero_right (a : Page X (k+1)) : seam a (0:Page X (n+1))=0 := by ext1 x; simp [seam]
lemma seam_scale (r : ℝ) : seam (r • a) b = seam a (r • b) ∧ seam a (r • b)=r • seam a b := by
  constructor <;> ext1 x <;> simp [seam] <;> ring
lemma seam_add_left : seam (a+a') b = seam a b + seam a' b := by ext1 v; exact add_mul ..
lemma seam_add_right : seam a (b+b') = seam a b + seam a b' := by ext1 v; exact mul_add ..
lemma seam_sub_left : seam (a-a') b = seam a b - seam a' b := by ext1 v; exact sub_mul ..
lemma seam_sub_right : seam a (b-b') = seam a b - seam a b' := by ext1 v; exact mul_sub ..
lemma seam_tele : seam a b-seam a' b' = seam (a-a') b + seam a' (b-b') := by rw [seam_sub_left, seam_sub_right]; abel

lemma Within.bound_mul {u v : Page X n} (ha : Within D σ p u) (hp : 0≤q) (hh : ∀ x,|v x|≤q) : Within D σ (q*p) (u*v) := by
  have ht := ha.scale q; rw [abs_of_nonneg hp] at ht
  refine ht.by_abs fun x=>?_
  dsimp only [Pi.mul_apply,Pi.smul_apply,smul_eq_mul]; rw [mul_comm (u x),abs_mul,abs_mul q,abs_of_nonneg hp]; gcongr; exact hh _
lemma Within.prod {u v : Page X n} (ha : Within D σ p u) (hb : Within D θ q v) (hp : 0≤θ) : Within D σ (q*p) (u*v) := by
  by_cases he : n=0
  · subst n; exact ⟨mul_nonneg hb.1 ha.1,(fun i=>Fin.elim0 i)⟩
  exact ha.bound_mul hb.1 (within_entry hb hp he)

end YM.WilsonBulk.Sheet
