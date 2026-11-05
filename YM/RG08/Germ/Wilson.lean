import YM.RG08.Germ.Foliage

/-! # Top stencils. Literal Wilson logarithmic action in signed chart.
   `Faith`: every admitted input/output full LOOP after removing constants
   has matching gauge-invariant analytic jets on all perfect tori. This is
   not a coordinate bound. Grade convention and consistency with r=0,1
   recorded here. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Exterior Precision Bloch Next.Free Work.F08 Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix Tree
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius InnerProductSpace Classical
variable {G : Gauge} {w : ℝ} {n r i j k : ℕ} {m : Side}

-- Include both sign permutations. Plaquette cover basis stenciled locally.
private abbrev sweets (G : Gauge) := PlaqAxes × Fin 4 × G.ColorIndex
private def ticket (p : PlaqAxes) : Fin 4→Cover×TypeFace 1 :=
    ![(0,coord p.val.1),(step p.val.1,coord p.val.2),(step p.val.2,coord p.val.1),(0,coord p.val.2)]
private def sugar (a : sweets G) : Option (Cover × Loc G 1) := some ((ticket a.1 a.2.1).1, (ticket a.1 a.2.1).2,a.2.2)
private def cane (G : Gauge) (p : PlaqAxes) (i : Fin 4) : Corn (sweets G)→L[ℝ] G.Color := LinearMap.toContinuousLinearMap {
    toFun x := WithLp.toLp 2 (fun j => x (p,i,j)),map_add' _ _ := rfl,map_smul' _ _ := rfl }
private def fond (p : PlaqAxes) (i : Fin 4) (x : Corn (sweets G)) := G.lieExp (cane G p i x)
private def pile (x : Corn (sweets G)) := ∑ j : PlaqAxes, G.price (fond j 0 x * (fond j 1 x *((fond j 2 x)⁻¹*(fond j 3 x)⁻¹)))
private lemma pila : AnalyticAt ℝ (pile (G:=G)) 0 := by
  have hh i : Army (fun x p => fond p i (x : Corn (sweets G))) 0 := fun p=> (G.exp_jet.comp (f:=cane G p i) (cane G p i).contDiff).contDiffAt
  exact (show ContDiffAt ℝ ω (pile (G:=G)) 0 from ContDiffAt.sum (fun i _ => matrix_price_jet (((hh 0).mul ((hh 1).mul ((hh 2).inv.mul (hh 3).inv))) i))).analyticAt
private lemma fond_at (p : PlaqAxes) (i : Fin 4) (x : Link G m) (z : Site m) :
    fond p i (seats sugar z x)=G.lieExp (arm G m 1 x (z+wrap m (ticket p i).1,(ticket p i).2)) := rfl
lemma restore (m : Side) : WilsonQ G m= atmosphere sugar pile m := by
  funext x; unfold WilsonQ atmosphere Wilson.energy; rw [Fintype.sum_prod_type]; apply sum_congr rfl; intro z _
  change _=pile _; apply sum_congr rfl; intro p _; congr 1; simp only [faceValue,square,travel,Step.read, Step.vec]; simp only [posDir,negDir,Step.used,Bool.false_eq_true, ↓reduceIte, mul_one,fond_at]; unfold input; simp_rw [Work.F03.represent_link]
  simp [ticket, ← sub_eq_add_neg]; rw [add_right_comm z,add_sub_cancel_right,add_sub_cancel_right]

def caramel (u : G.ColorIndex) (r) : Pot G r := breath (0,coord 0,u) sugar pile r
lemma sugar_paid (u : G.ColorIndex) (hw : 0≤w) : ∃ C : ℝ,0≤ C ∧ Glow (caramel u r) w C := breath_quote (ι:=sweets G) _ _ _ w hw
lemma sugar_value (u : G.ColorIndex) : Tunable (caramel u r) ∧ ∀ m, Tensor.coeff (WilsonQ G m) r 0= recital (caramel u r) m :=
  ⟨breath_tune (ι:=sweets G) ..,fun m=> by rw [restore]; exact Eq.symm (breath_proofs _ pila _ (0,coord 0,u) _ _|>.2)⟩
lemma picture_unique {f g : Link G m→ℝ} {V : Picture G r} (he : Recorded V f 0) (hp : Recorded V g 0) :
    Tensor.coeff f (r+1) 0=Tensor.coeff g (r+1) 0 := by
  unfold Tensor.coeff; rw [from_note f g _ ?_]
  apply relay_ext; intro p
  let i (j) := (p j).2.2; let b (j):=(p j).2.1; let v (j) := (p j).1
  change noteAt f _ (glyph v i b)=noteAt g _ (glyph v i b)
  exact ((record_exact ..).1 he v i b).trans ((record_exact ..).1 hp v i b).symm
lemma caramel_two (u : G.ColorIndex) : caramel u 2=quad G (hessian leader) := by
  let B:=quad G (hessian leader)
  have hm : Whole leader := ⟨_,_,zero_lt_one,leader_pay 1⟩
  obtain ⟨w,C,hw,H⟩:=hessian_whole hm
  have hs p : (hessian leader).acts p |>.IsSymm := by rw [hessian_acts hm]; exact k_symmetric (by simp)
  obtain ⟨hp,hF,hQ⟩:=quad_matches G _ H hw.le (fun p=> hs p)
  apply (sugar_value (r:=2) u).1.unique hF
  intro m; unfold stanza
  apply congr_arg Tensor.diagonal
  rw [← (sugar_value u).2 m, ← hF.pick m]
  refine picture_unique (outright G m|>.2.2) (according leader_safe (fun x y=>?_)); rw [← hessian_acts hm]; exact hQ m x y

def wilsonTop (u : G.ColorIndex) : Air G := fun e r=> if r=e+2 ∧ 0<e then caramel u r else 0
lemma top_gets (u : G.ColorIndex) : Gets (wilsonTop u) ∧ Halt (wilsonTop u) := by
  constructor
  · constructor
    · intro e r hV; unfold wilsonTop at hV; split at hV; next h => exact ⟨h.2, 0,by omega⟩
      exact (hV rfl).elim
    intro e r; unfold wilsonTop; split
    · obtain ⟨C,h,hV⟩:= sugar_paid (r:=r) u zero_le_one; exact ⟨(sugar_value u).1,_,_,one_pos,hV⟩
    exact ⟨Tunable.zero ..,Glows.zero⟩
  unfold Halt wilsonTop; simp
-- invariant analytic jets for each unscaled loop action (value subtracted).
-- `Q` Hessian-kernel passed separately to disallow rank-zero/1 confusion.
def sector (Q : Pot G 2) (E : Air G) (q r : ℕ) : Pot G r := match r with
  | 0=> 0
  | 1=> E (1+2*q-2) 1
  | n+2=> if n+2*q=0 then prolong (n+2) Q else E (n+2*q) (n+2)

def Faithful (Q : Pot G 2) (E : Air G) (m : Side) := ∀ q n,∃ f : Link G m → ℝ, Pointwise f ∧
      ∀ j ≤ n, Tensor.coeff f j 0=recital (sector Q E q j) m

lemma dawn_truth (u : G.ColorIndex) (m : Side) : Faithful (quad G (hessian leader)) (wilsonTop u) m := by
  intro q n; rw [← caramel_two]; cases q with
  | zero=>
    refine ⟨_, Wilson_witness,fun j hj=>?_⟩; have he := outright G m
    cases j with
    | zero=> ext1 a; rw [Tensor.coeff_apply_zero,he.1, sector, recital_zero]; rfl
    | succ j=>
      cases j with
      | zero=> rw [sector]; change Tensor.coeff _ 1 0=_; unfold wilsonTop; rw [if_neg (by omega),recital_zero]; ext1 v; simp [Tensor.coeff,iteratedFDeriv_one_apply,he.2.1]
      | succ j=>
        rw [(sugar_value u).2 m]; cases j with
        | zero=> rw [sector,if_pos (by decide),prolong_self]
        | succ j=>
          rw [sector,if_neg (by omega)]; unfold wilsonTop; rw [if_pos (by omega)]
  | succ q=>
    have hs := Wilson_witness (G:=G) (m:=m)
    refine ⟨0 • WilsonQ G m, hs.coin 0, ?_⟩ -- signature?
    intro j hj; rw [zero_smul]; change Tensor.coeff (fun _=>0) _ _=_
    rw [Tensor.coeff_zero]; match j with
    | 0=> rw [sector, recital_zero]
    | 1=> rw [sector,wilsonTop,if_neg (by omega),recital_zero]
    | j+2=> rw [sector,if_neg (by omega),wilsonTop,if_neg (by omega),recital_zero]
end YM.RG08
