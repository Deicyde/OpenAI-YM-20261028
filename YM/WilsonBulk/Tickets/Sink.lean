import YM.WilsonBulk.Tickets.Testing

/-!
# Shift/root split all legs. Invariance of joint zero moments under appending
  forced labels and under changing gauge meter. Usable at finite orders, not
  uniform gauge derivative. Identity with postage.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open Function Filter Finset Equiv Lattice Laurent RG Pert.Bulk Parapet
open scoped Topology BigOperators Classical ENNReal
open Taylor (lineRead league)
open MvPolynomial (X C eval rename aeval)
variable {α β γ : Type} {σ τ p q : ℝ} {n d k m : ℕ} {P U : Text α (n+1)}

-- slip represented by list of Covers; use Δ_y := true-positions MINUS head

def profile (c : Fin n) (x : Slip n) : Cover:= fun i=> x (c,i)
def cage (s : Cover) : Slip n := fun i=> s i.2
def vaults (s : Slip n) (x : Slip m) : Slip (n+m) := fun i=> Fin.append (fun j:Fin n=>profile j s) (fun j:Fin m=>profile j x) i.1 i.2
@[simp] lemma profile_cage (x : Cover) (j : Fin n) : profile j (cage x)=x := rfl
@[simp] lemma profile_add (x y : Slip n) (j : Fin n) : profile j (x+y) = profile j x+profile j y:= rfl
@[simp] lemma profile_neg (x : Slip n) (j : Fin n) : profile j (-x)= - profile j x := rfl
@[simp] lemma profile_sub (x y : Slip n) (j : Fin n) : profile j (x-y) = profile j x-profile j y:= rfl
lemma profiles_eq (x y : Slip n) (h : ∀ i,profile i x=profile i y) : x=y := funext fun i=> congr_fun (h i.1) i.2
lemma lamp_ish (x : Market α) (v : Slip n) (t : Legs α n) (i : Fin n) : put x.1 t v i=(x.1+profile i v,t i) := rfl
lemma enclaves (x a : Cover) (v : Slip n) (t : Legs α n) : put x t v = put a t (v-cage (a-x)) := by
  ext1 i; change (x+profile i v,_)= (a+profile i _, t i); simp; abel
lemma deposit (x : Slip n) (y : Slip m) : (fun i=> profile i (vaults x y))= Fin.append (fun i:Fin n=>profile i x) (fun i:Fin m=>profile i y):= rfl
lemma asset (t : Slip n) (u : Slip m) (x : Legs α n) (y : Legs α m) (c : Cover) :
    put c (Fin.append x y) (vaults t u)=Fin.append (put c x t) (put c y u) := by
  ext1 i; refine Fin.addCases (fun i=> ?_) (fun j=> ?_) i <;> simp [put,vaults,profile]
def harbor (n m : ℕ) : Slip n × Slip m ≃ Slip (n+m) where -- name Hallmark harbor, ok
  toFun p:= vaults p.1 p.2
  invFun u:= (fun i=> u (Fin.castAdd m i.1,i.2),fun i=>u (Fin.natAdd n i.1,i.2))
  left_inv u:= Prod.ext (funext fun i=>by simp [vaults,profile]) (funext fun i=>by simp [vaults,profile])
  right_inv u:= by ext1 ⟨j,i⟩; refine Fin.addCases (fun k=>?_) (fun k=>?_) j <;> simp [vaults,profile]

-- polynomial substitutions affine. Predictable shape

def outset (u : Slip n) : Formula (Keys n)→ₐ[ℝ] Formula (Keys n):= aeval (fun i=> X i+C ((u i:ℤ):ℝ))
lemma outset_read (u x : Slip n) (p : Formula (Keys n)) : lineRead x (outset u p)=lineRead (x+u) p := by
  change MvPolynomial.aeval (fun i=> (x i:ℝ)) (outset u p)=MvPolynomial.aeval _ p
  apply DFunLike.congr_fun (f:=(aeval (fun i=> (x i:ℝ))).comp (outset u)); ext1 i; simp [outset]
lemma outset_degree (x : Slip n) (p : Formula (Keys n)) : (outset x p).totalDegree ≤ p.totalDegree:= Taylor.aeval_downgrade (w:=fun i=> X i+C ((x i:ℤ):ℝ)) (fun i=> (MvPolynomial.totalDegree_add _ _).trans (by rw [MvPolynomial.totalDegree_C]; simp)) p
lemma slants (s : Slip m) (u : Formula (Keys (n+m))) :
    ∃ p:Formula (Keys n), p.totalDegree ≤ u.totalDegree ∧ ∀ v:Slip n,lineRead (vaults v s) u=lineRead v p := by
  let f : Keys (n+m)→ Formula (Keys n):=fun i=>Fin.addCases (fun j : Fin n=> X (j,i.2)) (fun j : Fin m=> C ((s (j,i.2):ℤ):ℝ)) i.1
  refine ⟨aeval f u,Taylor.aeval_downgrade (w:=f) ?_ u,fun v=>?_⟩; · rintro ⟨i,j⟩; refine Fin.addCases (fun i=> ?_) (fun i=>?_) i <;> simp [f,-map_intCast]
  change MvPolynomial.aeval (fun i=> (vaults v s i:ℝ)) u= _; symm; apply DFunLike.congr_fun (f:=(aeval (fun i:Keys n=> (v i:ℝ))).comp (aeval f)); ext1 ⟨i,j⟩; refine Fin.addCases (fun i=> ?_) (fun i=>?_) i <;> simp [f,profile,vaults]

-- TicketNull for orientation-first shift+tassel burden:
-- root x chosen. then y for V fixed. pole-means test any true-position stencil y.
lemma horizon_tail {P : Text α (n+1)} (h : TicketNull d P) (y : Market α) (c : Cover) (t : Legs α n) (p : Formula (Keys n)) (hp : p.totalDegree < d) :
    HasSum (fun v:Slip n=> P (hitch y (put c t v))*lineRead v p) 0 := by
  let x:Slip n:= cage (y.1-c); apply (Equiv.addRight x).hasSum_iff.mp
  refine (h y t (outset x p) ((outset_degree ..).trans_lt hp)).congr_fun fun u=>?_
  change P (hitch y (put c t (u+x))) * lineRead (u+x) p =_; rw [outset_read, enclaves (a:=y.1) c (u+x) t, show u+x-(cage (y.1-c))=u from add_sub_cancel_right _ _] -- name?
end YM.WilsonBulk.Sheet
