import YM.Dash.Limits
import YM.Dash.Slew
import YM.Extraction.Inherited


/-!
# All-spectator scopes before Smooth

Weights not capped. Picaboo can probe any finite other weights on actual
label part. Deriv identity on exactly these joint tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Dash
open Function Set Filter MeasureTheory Measure Complex Analysis Extraction
open scoped ContDiff Topology InnerProductSpace BigOperators
variable {G : Gauge} {L : Register G} {n : ℕ}

structure Shot (L : Register G) where
  n : ℕ
  i : Fin n
  left : Fin n → L.Token
  f : Test n

namespace Shot
variable (s : Shot L)

def record {d} (x : L.Ref d) := Function.update s.left s.i (⟨d,x⟩ : L.Token)

def insert {d} (x : L.Ref d) (S : Table L) (u : Points s.n) := S.read u (s.record x)

abbrev tape (s : Shot L) (d : ℕ) : Caps s.n := fun i => if i=s.i then d else (s.left i).1

def Tilt (L : Register G) (a b : ℕ) (h : a=b) : L.Ref a→ₗ[ℂ] L.Ref b := by subst b; exact LinearMap.id
lemma tilt (L : Register G) (a b : ℕ) (h : a=b) (x : L.Ref a) : Sigma.mk b (Tilt L a b h x)=⟨a,x⟩ := by subst b;rfl

def codes (s : Shot L) (d : ℕ) (x : L.Ref d) (i : Fin s.n) : L.Ref (s.tape d i) :=
  if h : i=s.i then (Tilt L d _ (Eq.symm (if_pos h))) x else (Tilt L (s.left i).1 _ (Eq.symm (if_neg h))) (s.left i).2

lemma plusTape {d} (x y : L.Ref d) : s.codes d (x+y) s.i=s.codes d x s.i+s.codes d y s.i := by
  simp [codes,map_add]
lemma timesTape {d} (c : ℂ) (x : L.Ref d) : s.codes d (c • x) s.i =c • s.codes d x s.i := by
  simp [codes,map_smul]
lemma cod {d} (x : L.Ref d) : (fun i => Sigma.mk (s.tape d i) (s.codes d x i))=s.record x := by
  classical
  funext i; by_cases h : i=s.i
  · subst i; unfold codes; rw [dif_pos rfl,tilt]; simp [record]
  simp only [codes,dif_neg h,record,update_of_ne h]; exact tilt L _ _ _ _
lemma gram {d} (x : L.Ref d) (i : Points s.n) (S : Table L) : s.insert x S i = S.value (s.tape d) i (s.codes d x) := by
  unfold insert; rw [← s.cod x]; rfl
lemma sameTape {d} (x y : L.Ref d) : s.codes d x = update (s.codes d y) s.i (s.codes d x s.i) := by
  funext i; by_cases h:i=s.i
  · subst i; rw [update_self]
  rw [update_of_ne h]; simp only [codes,dif_neg h]
lemma add {d} (x y : L.Ref d) (i : Points s.n) (S : Table L) : s.insert (x+y) S i=s.insert x S i+s.insert y S i := by
  simp_rw [s.gram]
  have he : s.codes d (x+y) s.i=s.codes d x s.i+s.codes d y s.i := s.plusTape _ _
  rw [s.sameTape (x+y) x,he, (S.value (s.tape d) i).map_update_add, ← s.sameTape,← s.sameTape]
lemma product {d} (c : ℂ) (x : L.Ref d) (i : Points s.n) (S : Table L) : s.insert (c • x) S i=c * s.insert x S i := by
  simp_rw [s.gram]
  have he : s.codes d (c • x) s.i=c • s.codes d x s.i := s.timesTape c x
  rw [s.sameTape (c • x) x,he, (S.value (s.tape d) i).map_update_smul, ← s.sameTape]; rfl
def core (s : Shot L) {d} (S : Table L) (h : Live S) : L.Ref d→L[ℂ] ℂ := LinearMap.toContinuousLinearMap {
  toFun p := s.f.applyTo fun x => s.insert p S x
  map_add' x y := by
    unfold Test.applyTo insert
    rw [← integral_add (h s.n (s.record x) s.f) (h s.n (s.record y) s.f)]; apply integral_congr_ae; filter_upwards with i
    rw [← mul_add]; congr 1
    exact Shot.add _ x y i _
  map_smul' c v := by
    change s.f.applyTo (s.insert (c • v) S) = c * s.f.applyTo _
    unfold Test.applyTo
    rw [← integral_const_mul]; congr! 2; rename_i i
    rw [mul_left_comm]; congr 1
    exact Shot.product _ c v i _ }

/-! evaluation at EVERY actual cutoff, Varying placements in smears
at one coordinate. Support tied in all n. -/
variable {C : Family G}
lemma from_finite (s : Shot C.book) (x : C.book.Ref n) (N p) : Extraction.Order.smears C N p (s.record x) s.f=(C.S.a N:ℂ)^(4*s.n)*
    ∑ r : Fin s.n → Lattice.Site (C.side N p), s.f (Order.cells C N p r)* (C.ensemble (s.tape n) r) (s.codes n x) := by
  rw [Order.smears, ← s.cod x]; rfl

def scan (s : Shot C.book) (d N p : ℕ) : C.book.Ref d→L[ℂ] ℂ := LinearMap.toContinuousLinearMap {
  toFun x := Extraction.Order.smears C N p (s.record x) s.f
  map_add' x y := by
    simp_rw [from_finite]
    rw [← mul_add,← Finset.sum_add_distrib]; congr 1
    apply Finset.sum_congr rfl; intro i _; rw [← mul_add]; congr 1
    rw [s.sameTape (x+y) x,s.plusTape,
      MultilinearMap.map_update_add, ← s.sameTape,← s.sameTape]
  map_smul' c x := by
    simp_rw [from_finite]
    change _= c*(_*_); rw [mul_left_comm c _ _,Finset.mul_sum _ _ c]; congr 1
    apply Finset.sum_congr rfl; intro i _; rw [mul_left_comm]; congr 1
    rw [s.sameTape (c•x) x, s.timesTape,
      MultilinearMap.map_update_smul,← s.sameTape]; rfl }

lemma ready (s : Shot C.book) {f : Order} {S : Table C.book} (h : Live S) (hx : f.Ordered C S) (d) : Tendsto
    (fun i : ℕ × ℕ => s.scan d i.1 i.2) f.fuse (𝓝 (s.core (d:=d) S h)) := by
  suffices HE : Tendsto (fun i : ℕ × ℕ => LinearMap.toContinuousLinearMap (s.scan d i.1 i.2).toLinearMap) f.fuse (𝓝 (LinearMap.toContinuousLinearMap (s.core (d:=d) S h).toLinearMap)) by exact HE
  refine fit_plane (fun i : ℕ × ℕ => (s.scan d i.1 i.2).toLinearMap) (s.core (d:=d) S h).toLinearMap ?h
  intro v
  have he := Order.along (hx.reads s.n (s.record v) s.f)
  exact he
end Shot

def monitor (S : Table L) (h : Live S) (d : ℕ) := ⨅ i : Shot L, LinearMap.ker (i.core (d:=d) S h).toLinearMap

theorem notices (S : Table L) (h : Live S) {d} (p : L.Ref d) : p∈ monitor S h d ↔ S.vanishes d p := by
  rw [monitor,Submodule.mem_iInf]; constructor
  · intro he n w i hv t
    have ht := he (Shot.mk n i w t)
    let g := (⟨n,i,w,t⟩ : Shot L)
    change t.applyTo (fun x => S.read x (g.record p))=0 at ht
    rw [show g.record p=w by simp [Shot.record,g,←hv]] at ht; exact ht
  exact fun H i => H i.n (i.record p) i.i (by simp [Shot.record]) i.f

def Bin (_S : Table L) := (d : ℕ) → Branch (L.Ref d) (ℕ × ℕ)
namespace Bin
variable {S : Table L}
abbrev Matrix (p : Bin S) (d : ℕ) (f : Order) := approaches f.fuse (p d)
abbrev Good (p : Bin S) (h : Live S) (d : ℕ) := verified (p d) (fun i : Shot L => i.core S h)

lemma transfer (p : Bin S) (h : Live S) {T : Table L} (hv : matchReg S T) (hx : T.Symmetric) (hp : T.Smooth) (d)
    (he : Good p h d) : T.null d=LinearMap.ker (p d).trueP.toLinearMap := by
  ext x
  rw [T.equivalent hp hx,show LinearMap.ker _=monitor S h d from he, notices S h]
  unfold Table.vanishes
  simp_rw [faithful hv]
end Bin
end YM.Dash
