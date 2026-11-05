import YM.Climb.Cells

/-!
# Test matrices consumed after weak data, finite Ward part
-/
set_option autoImplicit false
noncomputable section
namespace YM.Climb
open Function Set Filter MeasureTheory Measure Complex Analysis Extraction Table Ward Spin
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {L : Register G} {S : Table L} {n d e : ℕ}

/-- all `v : S.Field d`. Filtration caps homogeneous labels. -/
def column (v : Fin n → S.Field d) := fun i => (⟨d,v i⟩ : S.Tag)

def diagram (v : Fin n→ S.Field d) (q : Matrix d e S) (x : Points n) :=
    ∑ k, disc (update (column v) k (⟨e,q (v k)⟩ : S.Tag)) x

def observed (v : Fin n → S.Field d) (x : Points n) (e : ℕ) : Matrix d e S →ₗ[ℂ] ℂ :=
    ∑ i : Fin n, (here (column v) x i e).comp (ContinuousLinearMap.apply ℂ (S.Field e) (v i)).toLinearMap
lemma observation (v : Fin n→ S.Field d) (q : Matrix d e S) (x : Points n) : observed v x e q=diagram v q x := by
  unfold diagram observed; simp only [LinearMap.sum_apply]; apply Finset.sum_congr rfl; intro i _; exact takes ..

structure Scene (S : Table L) (d : ℕ) where
  n : ℕ
  v : Fin n→ S.Field d
  a : Axis
  b : Axis
  offAxis : b≠a
  x : Points n
  strict : x ∈ conf n
  positions : onLine a x
  m : ℕ
  dirs : Fin m → Points n

namespace Scene
variable (X : Scene S d)

def lens (p : Vector d S) : ℂ := iteratedFDeriv ℝ X.m (diagram X.v (p X.b)) X.x X.dirs
end Scene
namespace Scaling
variable (p : Scaling S)

def carry (k : ℕ) (t : Matrix d e S) : Matrix d e (Bel L) := LinearMap.toContinuousLinearMap
    ((p.U k e).symm.toLinearMap.comp (t.toLinearMap.comp (p.U k d).toLinearMap))
@[simp] lemma carries_f (x : (Bel L).Field d) (t : Matrix d e S) (k) :
    p.U k e (p.carry k t x)=t (p.U k d x) := (p.U k e).apply_symm_apply _

def aisle (k : ℕ) (d) : Vector d S→ₗ[ℝ] Vector d (Bel L) where
  toFun v := fun a => p.carry k (v a)
  map_add' x y := by
    ext1 i; ext1 v; change p.carry k _ v=p.carry k _ v+p.carry k _ v; apply (p.U k _).injective; simp
  map_smul' a x := by
    ext1 i; ext1 v; apply (p.U k (d+1)).injective
    change p.U k _ (p.carry k _ _)=p.U k _ (a • p.carry k (x i) v)
    have he (U : (Bel L).Field (d+1)) : p.U k (d+1) (a • U) = a • p.U k (d+1) U := ((p.U k _).toLinearMap.restrictScalars ℝ).map_smul _ _
    rw [he,carries_f,carries_f]; rfl

lemma aisle_ext (k : ℕ) (d : ℕ) : Injective (p.aisle k d) := by
  intro x y he
  ext1 i; ext1 v
  obtain ⟨u,rfl⟩ := (p.U k _).surjective v
  rw [← p.carries_f u (x i),← p.carries_f u (y i)]; exact congr_arg (fun g : Vector d _ => p.U k (d+1) (g i u)) he

lemma toColor {D : ℕ} {W : DiffPlan S} {T : DiffPlan (Bel L)} {H a} (hp : p.Align W T H a D)
    {t : Vector d S} (hc : t∈Colors W H d) (hd : d<D) (k : ℕ) : p.aisle k d t∈ Colors T a d := by
  obtain ⟨A,B,C⟩ := hc
  refine ⟨fun i => ⟨?_,?_⟩,fun i s v => ?_,fun i v => ?_⟩
  · apply (p.U k (d+1)).injective
    change p.U k _ (p.carry _ _ _)=_
    rw [p.carries_f,hp.carries k d hd.le,map_zero]; exact (A i).1
  · intro i' hu v
    obtain ⟨y,hy⟩ := (A i).2 i' hu (p.U k i' v)
    obtain ⟨u,rfl⟩ := (p.U k _).surjective y
    refine ⟨u,(p.U k _).injective ?_⟩
    change p.U k _ _=p.U k _ (p.carry k _ _); rw [p.carries_f,hp.incl k i' d hu hd.le,hp.incl k _ _ _ hd]; exact hy
  · change (Bel L).mirror _ _ _ (p.carry k _ _) = ∑ j : Axis, _ • (p.carry k (t j) ((Bel L).mirror _ d _ _))
    apply (p.U k _).injective
    set u := p.U k d v
    rw [(hp.Hsym k _ hd).1, p.carries_f,B]; rw [_root_.map_sum]; simp only [map_smul,p.carries_f,(hp.Hsym k d hd.le).1]
  apply (p.U k _).injective
  rw [(hp.Hsym k _ hd).2]; change S.conj _ _ (p.U k _ (p.carry _ _ _))= p.U k _ (p.carry _ _ _); rw [carries_f,carries_f,(hp.Hsym k d hd.le).2,C]

/-- actual rescaled matrix entries evaluated on free vectors -/
def test (k : ℕ) (s : Scene (Bel L) d) (T : Vector d (Bel L)) : ℂ :=
    iteratedFDeriv ℝ s.m (fun x => ∑ i, disc (p.pins k ∘ update (column s.v) i (⟨_,T s.b (s.v i)⟩ : (Bel L).Tag)) (p.r k • x)) s.x s.dirs

end Scaling
/-!
Finite rows extraction. Inputs through all same d filtration. Armed
maps computed on diagrams; only need converge finite, not all selectors.
-/
abbrev V0 (L : Register G) (d : ℕ) := Vector d (Bel L)

structure Select (L : Register G) (d : ℕ) where
  m : ℕ
  rows (i : Fin m) : Scene (Bel L) d
  reads : V0 L d →L[ℝ] (Fin m→ℂ)
  stimulated i p : reads p i=(rows i).lens p

structure Ens (P : Select L d) (K : DiffPlan (Bel L)) (h : (Bel L).RealSpin) : Prop where
  vec : leaves K.deriv d∈ Colors K h d
  nz : leaves K.deriv d ≠ 0
  identifies (v : V0 L d) : v ∈ Colors K h d → (P.reads v=0 ↔ ∃ c : ℝ, v=c • leaves K.deriv d)

structure Subs (P : Select L d) (p : Scaling S) where
  moves (k : ℕ) : V0 L d→L[ℝ] (Fin P.m→ℂ)
  values k i s : moves k s i=p.test k (P.rows i) s

end YM.Climb
