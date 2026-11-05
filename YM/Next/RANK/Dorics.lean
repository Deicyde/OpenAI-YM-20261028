import YM.Next.RANK.Walked

/-!
# Gauge at joint stencils, color ledger
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Finset
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {o : Side}
variable {S : Schedule} {C : Family G} {A : Levels G} {i k l j m p q n D N d : ℕ}
-- paper for current stage coordinates (offset--linear curves). Only global rigid Ad, torus-facing.

abbrev bead (G : Gauge) (o : Side) := Site o × PlaqAxes × G.ColorIndex

def fromBead (G : Gauge) (i : bead G o) : Face (Per o) := (i.1,i.2.1)
def position (s : Cover) (p : slotC G i) : bead G o:= (wrap _ (s+p.1.val.1), p.1.val.2,p.2)
lemma primeVisit (P : AtlasData G S p) (F : poly (slotC G i)) (h : 4*i≤d) (s : Cover) (k) : lifted P F s k h=rename (position s) F:= MvPolynomial.rename_rename ..

def rigid (p : Face (Per o) → G.Color) (i : bead G o): ℝ:= p (fromBead G i) i.2.2

def coloration (o : Side) (u : G.El) (i : bead G o) : bead G o →₀ ℂ:= ∑ j : G.ColorIndex,Finsupp.single (i.1,i.2.1,j) (↑(G.adjoint u (EuclideanSpace.basisFun _ ℝ j) i.2.2))
lemma colours (x : Face (Per o)→ G.Color) (P : poly (bead G o)) (u : G.El) : text (rigid (coloring u x)) P=text (rigid x) (exchange (coloration o u) P):= by
  apply DFunLike.congr_fun (g:= (aeval (R:=ℂ) _).comp (exchange (coloration o u))); ext1 i; simp only [aeval_X,AlgHom.comp_apply, exchange_x, glyph, coloration,_root_.map_sum,Finsupp.linearCombination_single,_root_.map_smul,aeval_X]
  unfold rigid coloring
  let B:= (EuclideanSpace.basisFun G.ColorIndex ℝ).toBasis
  let w:= x (fromBead G i)
  have he : w=∑ j,B.repr w j • B j := (B.sum_repr _).symm
  have hv j : B.repr w j=w j := by dsimp only [B];simp
  conv_lhs => rw [show x (fromBead G i)=_ from he,_root_.map_sum]
  simp_rw [map_smul]
  rw [show ∀ g : G.ColorIndex → G.Color,(∑ i,g i).ofLp i.2.2=∑ j,(g j).ofLp i.2.2 from fun g => map_sum (EuclideanSpace.proj i.2.2 : G.Color →L[ℝ] ℝ) g _,Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _=> ?_; rw [hv]; change ((↑( (w j:ℝ)*((G.adjoint u) (B j)) i.2.2 ):ℂ))= _; rw [Complex.ofReal_mul]; exact mul_comm ..
def Poetic (P : poly (bead G o)) : Prop := ∀ u : G.El, exchange (coloration o u) P=P

lemma poetry (F : poly (slotC G i)) (h : Spirit F) (s: Cover) (o : Side): Poetic (o:=o) (rename (position s) F):= by
  have ht (u):exchange (paper G u i) F=F := by
    apply audible; intro v; let g:Turn i→G.Color := fun i=> WithLp.toLp 2 (fun j=>v (i,j))
    exact (salute g u F).symm.trans (h g u).symm
  intro u
  let R:= rename (position (G:=G) (i:=i) (o:=o) s) (R:=ℂ)
  have hv : (exchange (coloration o u)).comp R = R.comp (exchange (paper G u i)):= by
    ext1 j; let a:= position (o:=o) s j; rw [AlgHom.comp_apply, AlgHom.comp_apply, Normal.exchange_x, show R (X j) = X a from rename_X ..,Normal.exchange_x]; unfold coloration paper glyph; rw [map_sum,map_sum,_root_.map_sum]; apply Finset.sum_congr rfl; intro k _; rw [Finsupp.linearCombination_single,Finsupp.linearCombination_single,map_smul,show ∀ x : slotC G i,R (X x) = X (position s x) from fun x=> rename_X ..]; rfl
  exact (show exchange (coloration o u) (R F) = R (exchange (paper G u i) F) from DFunLike.congr_fun hv F).trans (congr_arg R (ht u))
-- H and Q act. Types before basis comparisons

structure Voice (R : Lead G S p) (j : ℕ) : Prop where
  path (u : G.El) :
    let Q:= exchange (R j).H
    Q.comp (exchange (coloration (S.side (j+1) p) u))= (exchange (coloration (S.side j p) u)).comp Q
  tune (u : G.El) : Normal.scope (coloration _ u) (R j).Q=(R j).Q

lemma sung (R : Lead G S p) (P : poly _) (h : j≤k) (he : ∀ i, j ≤ i → i<k → Voice R i) (hp : Poetic (o:=S.side k p) P) : Poetic (shelve R h P):= by
  induction h using Nat.decreasingInduction with
  | self=> rw [center_shelf]; exact hp
  | of_succ i hi ih=>
    rw [shelving R hi]; have ht:=he i le_rfl hi; have hv:=ih (fun j hj=> he j (by omega))
    let Q:=R i; let V:= exchange Q.H; let S:= shelve R (show i+1≤k from hi) P
    intro u
    change exchange _ (V (milk Q.Q S))= _
    rw [show exchange _ (V _)= V (exchange _ (milk Q.Q S)) from DFunLike.congr_fun (ht.path u).symm (milk Q.Q S)]
    refine congr_arg V ?_
    rw [← show milk (Normal.scope (coloration _ u) Q.Q) S=milk Q.Q S by rw [ht.tune], ← Normal.prepared, hv,ht.tune]

lemma verses (R : Lead G S p) (P) (h : j≤k) (he : ∀ i, j ≤ i → i<k → Voice R i) (hp : ∀ i, Poetic (o:=S.side k p) (P i)) (x : pennant n): Poetic (polygon R P h x) := by
  cases x with
  | inl x=> exact sung R _ h he (hp x)
  | inr x=>
    have hf : Poetic (twoRoot R P h x):= sung R _ h he (fun u=> by rw [map_mul,hp _,hp _])
    intro u; rw [polygon,_root_.map_sub,map_mul,hf u]
    congr 1; unfold oneRoot; rw [sung R _ h he (hp _) u, sung R _ h he (hp _) u]
end YM.Next.Rank.Tapes
