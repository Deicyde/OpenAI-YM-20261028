import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.LinearAlgebra.Trace
import YM.Ac.Nodes
import YM.Gauge.MatrixGroup

/-!
# sharp polymer recursion without order-divisions

No sum over cuts. Label use at most once in the component.
Does not apply to Mayer LOG arrays allowing arbitrary repetition.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Ac
open Relation Lattice  Finset
open scoped Classical
variable {ι : Type*} [DecidableEq ι] {n : Side} (X : ι → Support n)

def pouch (D : Finset ι) (Y : Support n) := D.powerset.filter (Pack X Y)
variable (D : Finset ι) (Y : Support n)

omit [DecidableEq ι] in
lemma op {s} : s∈pouch X D Y ↔ s ⊆ D ∧ Pack X Y s := by simp [pouch]

def buds := D.filter (fun i => meets X i Y)

omit [DecidableEq ι] in
lemma alive {i} : i∈ buds X D Y ↔ i∈ D ∧ meets X i Y := by simp [buds]

private abbrev C := ↥(buds X D Y)
private abbrev Box (i : C X D Y) := Option ↥(pouch X (D.erase i.val) (X i.val))
private abbrev Fl := (i : C X D Y) → Box X D Y i

private abbrev P := ↥(pouch X D Y)
private abbrev shoots (s : P X D Y) := ↥(Parts X s.val)

private lemma wins (s : P X D Y) (p : shoots X D Y s) : ∃ i : C X D Y, i.val∈p.val := by
  obtain ⟨h1,h2⟩:= (op _ _ _).mp s.property; obtain ⟨i,hi,hj⟩ := packHits X h2 p.val p.property
  exact ⟨⟨i,(alive _ _ _).mpr ⟨h1 ((lives X s.val p.property).1 hi),hj⟩⟩,hi⟩
private def eye (s : P X D Y) (p : shoots X D Y s) := (wins X D Y s p).choose
private theorem spot (s : P X D Y) (p : shoots X D Y s) : (eye X D Y s p).val ∈ p.val := (wins X D Y s p).choose_spec
private theorem sight (s : P X D Y) : Function.Injective (eye X D Y s) := by
  intro p q he; have hh := spot X D Y s p; rw [he] at hh
  apply Subtype.ext; apply (contains X p.property _ hh).symm.trans (contains X q.property _ (spot X D Y s q))
private def boxRead (s : P X D Y) (p : shoots X D Y s) : ↥(pouch X (D.erase (eye X D Y s p).val) (X (eye X D Y s p).val)) :=
  ⟨p.val.erase (eye X D Y s p).val,(op _ _ _).mpr ⟨erase_subset_erase _ (by
    intro i hi; exact ((op _ _ _).mp s.property).1 ((lives X s.val p.property).1 hi)),excise X (lives X s.val p.property).2 (spot X D Y s p)⟩⟩
private def takePack (s : P X D Y) : Fl X D Y := fun i => if h : ∃ j, eye X D Y s j=i then
      h.choose_spec ▸ (some (boxRead X D Y s h.choose)) else none
private lemma takes (s : P X D Y) (p : shoots X D Y s) : takePack X D Y s (eye X D Y s p)=some (boxRead X D Y s p) := by
  unfold takePack
  let h : ∃ j,eye X D Y s j=eye X D Y s p := ⟨p,rfl⟩
  rw [dif_pos h]
  exact (show ∀ j, ∀ H : eye X D Y s j=eye X D Y s p, H ▸ (some (boxRead X D Y s j)) = some (boxRead X D Y s p) from fun j H => by
    have hx := sight X D Y s H; subst j; rfl) _ _
private def portion (i : C X D Y) : Box X D Y i → Finset ι
  | none => ∅
  | some s => insert i.val s.val

private lemma take_inj : Function.Injective (takePack X D Y) := by
  have he (s : P X D Y) : univ.biUnion (fun i => portion X D Y i (takePack X D Y s i))=s.val := by
    ext x; constructor
    · intro hx; obtain ⟨i,-,h⟩ := mem_biUnion.mp hx
      by_cases hh : ∃ p,eye X D Y s p=i
      · obtain ⟨p,rfl⟩ := hh
        rw [takes] at h; unfold portion boxRead at h; change x∈insert _ _ at h; rw [insert_erase (spot X D Y s p)] at h
        exact (lives X s.val p.property).1 h
      simp [portion,takePack, hh] at h
    intro h
    rw [← reconstruct X s.val] at h; obtain ⟨p,hp,H⟩ := mem_biUnion.mp h
    let i : shoots X D Y s := ⟨p,hp⟩
    apply mem_biUnion.mpr; refine ⟨eye X D Y s i,mem_univ _,?_⟩
    rw [takes]; change x∈insert _ (i.val.erase _); rwa [insert_erase (spot X D Y s i)]
  intro s t h; apply Subtype.ext; rw [← he s,← he t,h]

variable (f : ι → ℝ)

def film := ∑ s∈pouch X D Y, ∏ i ∈ s,f i

lemma lookup (hh : ∀ i, 0≤ f i) : film X D Y f ≤ ∏ i∈buds X D Y,(1+f i*film X (D.erase i) (X i) f) := by
  let e := fun (i : C X D Y) (b : Box X D Y i) => ∏ k∈portion X D Y i b,f k
  let g := fun t : Fl X D Y => ∏ i, e i (t i)
  have he (s : P X D Y) : (∏ i∈s.val,f i)=g (takePack X D Y s) := calc
    _ = ∏ p ∈ Parts X s.val, ∏ i∈p,f i := by
      simpa only [reconstruct,id_eq] using prod_biUnion (different X s.val) (f:=f)
    _ = ∏ p : shoots X D Y s, ∏ i∈p.val,f i := prod_subtype _ (by intros; rfl) _
    _ = ∏ p : shoots X D Y s, e (eye X D Y s p) (takePack X D Y s (eye X D Y s p)) := by
      apply prod_congr rfl; intro p _; rw [takes]
      simp only [e,portion,boxRead,insert_erase (spot X D Y s p)]
    _ = ∏ i ∈ univ.image (eye X D Y s),e i (takePack X D Y s i) := by rw [prod_image (sight X D Y s).injOn]
    _ = _ := prod_subset (subset_univ _) (by
        intro i hi h
        simp only [mem_image, mem_univ,true_and] at h
        simp [e,takePack,h,portion])
  have hw (i : C X D Y) : (∑ j,e i j) = 1+f i.val*film X (D.erase i.val) (X i.val) f := by
    rw [Fintype.sum_option]; dsimp only [e,portion]; rw [prod_empty]; congr 1; unfold film
    rw [sum_subtype (p:=fun s => s ∈ pouch X _ _) _ (fun _ => Iff.rfl),mul_sum]; apply sum_congr rfl; intro p _
    apply prod_insert; exact fun hn => notMem_erase i.val D (((op _ _ _).mp p.property).1 hn)
  unfold film
  calc
    _ = ∑ s : P X D Y, ∏ i∈s.val,f i := sum_subtype _ (by intros; rfl) _
    _ = ∑ s∈ univ.image (takePack X D Y), g s := by rw [sum_image (take_inj X D Y).injOn]; exact sum_congr rfl fun i _ => he i
    _ ≤ ∑ s, g s := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => prod_nonneg fun _ _ => prod_nonneg fun j _ => hh j)
    _ = ∏ i : C X D Y, (1+f i.val*film X (D.erase i.val) (X i.val) f) := by simp_rw [g, ← Fintype.prod_sum,hw]
    _ = _ := (prod_subtype (p:=fun i => i ∈ buds X D Y) _ (fun _ => Iff.rfl) (fun i=> 1+f i*film X (D.erase i) (X i) f)).symm
end YM.Ac
