import YM.UVExtension.Limits
import Mathlib.Analysis.Normed.Module.FiniteDimension
import YM.Next.STATIONARY.Infrastructure.Jets

/-! Two uses: obtain polynomial sensitivity degree even on gigantic finite domains; and obtain
common-sequence stability of station outputs across cutoffs. Keep prices of the latter only for fixed data. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Projection
open Filter Function Finset
open scoped Topology BigOperators ContDiff Classical
variable (I : Type)
structure MenuView where
    pace : ℕ → (I→ℝ) → Prop
    base (d : ℕ) (v : ℝ) : pace d (fun _=> v)
    mono {d k : ℕ} {f : I→ℝ} : pace d f → d ≤ k→ pace k f
    add {d : ℕ} {f g : I →ℝ}: pace d f → pace d g→ pace d (f+g)
    mul {d e : ℕ} {f g : I →ℝ}: pace d f → pace e g → pace (d+e) (f*g)
    post {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {f : I→X}
      {p : X→ℝ} {s : Set X} : (∀ L : X →ₗ[ℝ] ℝ,pace 0 fun i=> L (f i)) → (∀ i, f i∈s)→ IsClosed s → ContinuousOn p s → pace 0 fun i=> p (f i)
namespace MenuView
open Module
variable {I} (P : MenuView I)
variable {X Y : Type} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] {f g : I→ X} {d s : ℕ}
def sees (d : ℕ) (f : I→X):= ∀ L : X →ₗ[ℝ] ℝ,P.pace d fun i=> L (f i)
variable {P}
lemma steady (P : MenuView I) (j : ℕ) (x : X): P.sees j fun _=>x:= fun _=> P.base _ _
lemma sees_up (h : P.sees d f) (hh : d≤s): P.sees s f:=fun L=> P.mono (h L) hh
lemma acts (h : P.sees d f) (L : X→ₗ[ℝ] Y): P.sees d fun i=> L (f i):=fun M=> h (M.comp L)
lemma joins (h : P.sees d f) (he : P.sees d g): P.sees d (fun i=> f i+g i):= by intro L; simp_rw [map_add]; exact P.add (h L) (he L)
lemma scales {p : I→ℝ} (h : P.pace s p) (he : P.sees d f):P.sees (s+d) (fun i=> p i • f i):=by intro L; simp_rw [map_smul]; exact P.mul h (he L)
lemma book {f : I→ℝ}: P.sees d f ↔ P.pace d f:= by
  refine ⟨fun h=> h LinearMap.id,fun h L=>?_⟩
  have hp: P.pace (d+0) (f * fun _=> L 1):= P.mul h (P.base 0 _)
  refine (show (f * fun _=> L 1)=(fun i=> L (f i)) from funext fun i=> ?_) ▸ hp
  exact ((map_smul L (f i) (1:ℝ)).symm.trans (by simp))
lemma aggregated {J : Type*} (u : Finset J) (f : I → J → X) (h : ∀ j∈u, P.sees d (fun i=> f i j)): P.sees d fun i=> ∑ j∈u, f i j:=by
  induction u using Finset.induction with
  | empty => simp only [sum_empty]; exact steady P _ _
  | insert i u hi ih => simp_rw [sum_insert hi]; exact joins (h i (mem_insert_self ..)) (ih fun k hk=> h k (mem_insert_of_mem hk))
lemma sees_both {x : I → Y} (h : P.sees d f) (he : P.sees d x) : P.sees d fun i=>(f i,x i):= by
  simpa using (joins (acts h (LinearMap.inl ℝ X Y)) (acts he (LinearMap.inr ℝ X Y))) -- adapt
end MenuView
namespace MenuView
open Module
variable {I} {P : MenuView I}
variable {X Y E : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ X]

lemma crossing {f : I→X} {g : X→Y} {s : Set X} [FiniteDimensional ℝ Y] (h : P.sees 0 f) (he : ∀ i,f i∈s) (hp : IsClosed s) (hv : ContinuousOn g s):
    P.sees 0 fun i=> g (f i):= fun L=> P.post (p:=L∘g) h he hp ((L.continuous_of_finiteDimensional).comp_continuousOn hv)

lemma scalar_product {α : Type} [Fintype α] (U : I→ α→ℝ) (j : α→ℕ) (h : ∀ i,P.pace (j i) (fun n=> U n i))(s : Finset α): P.pace (∑ i ∈ s,j i) fun p=> ∏ i∈ s,U p i:=by
  induction s using Finset.induction with
  | empty=>simp; exact P.base _ _
  | insert i s he ih=> simp_rw [sum_insert he,prod_insert he]; exact P.mul (h i) ih

lemma multi (n : ℕ) (T : I → YM.Tensor.T X Y n) (x : I→ Fin n→ X) (r : Fin n→ℕ) {s : ℕ}
    (h : ∀ v,P.sees s fun i=> T i v) (he : ∀ j,P.sees (r j) fun i=> x i j): P.sees ((∑ j,r j)+s) fun i=> T i (x i):=by
  let e:= Module.finBasis ℝ X; let α:= Fin (finrank ℝ X); let u i j (p:α):= e.repr (x i j) p
  have hh i : T i (x i)=∑ p : Fin n→ α, (∏ j,u i j (p j)) • T i (fun j=> e (p j)):= by
    let g (j:Fin n) (p:α):=u i j p • e p
    rw [show x i= (fun j=> ∑ p,g j p) from (funext fun j => (e.sum_repr _).symm),ContinuousMultilinearMap.map_sum]
    exact sum_congr rfl fun b _=> (T i).map_smul_univ (fun j=>u i j (b j)) (fun j=> e (b j))
  simp_rw [hh]; refine aggregated univ _ fun i _=> scales (scalar_product _ _ (fun j=> ?_) _) (h _); exact he j (e.coord _)
end MenuView
end YM.UVExtension.Projection
