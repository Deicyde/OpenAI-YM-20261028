import YM.RG08.Cairn.Veil
/-!
# Library dispatch at one level and post-price alignment. r indexed from 0 represents r+2.
 e coupling with r≤e same parity. All-orders schemata with restriction by restricting requests;
 no infinite sums of coupling grades besides viewing as coefficients of a Cabin.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Mount
open Filter Lattice RG Wilson Forms Pert.Bulk Isles Camera Carrel Glyph Room Exterior Function
open Stationary Bloch Laurent Precision Line Finset Bid Work.F03 Matrix
open Tack Rudder Aggregate Symmetry Steam Cairn
open scoped BigOperators Classical ContDiff Topology Matrix Matrix.Norms.Frobenius NNReal InnerProductSpace PowerSeries
variable {G:Gauge}{c f:Side}{S:StepData c f}{P:Patch}{K:KernelChoices}{I J:Type}{n e:ℕ}

abbrev rank (r:ℕ):=r+2
abbrev Castle (G:Gauge) :=(r:ℕ) → (e:ℕ)→Rudder.Raw G.ColorIndex (rank r)
def Live (r e:ℕ):Prop:= r≤e ∧ Even (r+e)
structure Stable (C:Castle G) where
 dark r e : ¬ Live r e → C r e=0
 width : ℕ→ℕ→ℝ
 toll : ℕ→ℕ→ℝ
 dial r e:0<width r e
 weight r e:0≤toll r e
 banner r e : Cloak (dressed G (rank r)) 2 (C r e) -- exact type check
 hold r e : Held (carpet _) (width r e) (toll r e) (C r e)

def stick (r:ℕ):Fin (rank r):=0 -- inst neZero? r+1+1

def flight (r f:ℕ)(C:Rudder.Raw G.ColorIndex (rank r))(n:ℕ)(k:ℕ):Flake k (Market (Loc G 1)):= if f≤n ∧ n-f+rank r=k then completed C (stick r) k else 0
-- to fixed e; n+1 cutoff sufficient since Live

def demand (C:Castle G):Grain (Market (Loc G 1)) := fun n k=> ∑ i∈range (n+1), ∑ r∈range (i+1), flight r i (C r i) n k
-- universal finite version and view. scalars ignored

def unveil (R:Grain (Market I))(P:Side):Grain (Cove P I) :=fun k n=> if h:0<n then pour (R k n) ⟨0,h⟩ else 0
lemma unsealed (R:Grain (Market I))(P:Side)(k n)(o:Fin n)(hr:Cohort (R k n)):unveil R P k n=pour (R k n) o:=by rw [unveil,dif_pos o.pos];exact funext (fun i=> Isles.common hr _ _ i)
lemma blank (F:Flake n (Market I))(o:Fin n)(hf:F=0): pour (P:=c) F o=0:=by subst hf; ext i;rw [pour_at];simp
lemma unblocked (F:Grain (Market I))(e k)(hf:F e k=0):unveil F c e k=0:=by unfold unveil;split <;> rename_i h;exact blank _ _ hf;rfl

lemma flight_join {r m:ℕ}{C:Rudder.Raw G.ColorIndex (rank r)}{σ p:ℝ}(he:0<σ)(hp:0≤p)(h:Held (carpet _) σ p C):(Cohort (flight r m C e n)) ∧ (Forms.Sym (flight r m C e n)):=by
 unfold flight; split; next hh =>
    obtain ⟨p0,_,hh⟩:=completed_held G n (stick r) he
    exact ⟨(hh _ hp h).2.2,(hh _ hp h).2.1⟩
 exact ⟨fun _ _=>rfl,Forms.Sym.zero⟩
lemma Sym.sum {J:Type}(s:Finset J)(F:J→Flake n I)(h:∀ j∈s,Forms.Sym (F j)):Forms.Sym (s.sum F):=fun e=>funext fun i=>by unfold woven; simp only [Finset.sum_apply];apply sum_congr rfl; intro j hj;exact congrFun (h _ hj e) i
lemma demand_solid {C:Castle G}(h:Mount.Stable C)(e n): Cohort (demand C e n) ∧ Forms.Sym (demand C e n):=by
 have he r k:=flight_join (e:=e) (n:=n) (m:=k) (h.dial r k) (h.weight r k) (h.hold r k)
 exact ⟨Cohort.sum _ _ (fun i _=>Cohort.sum _ _ (fun r _=> (he r i).1)), Mount.Sym.sum _ _ (fun i _=> Mount.Sym.sum _ _ (fun r _=> (he r i).2))⟩
-- missing live
lemma completed_null (r:ℕ)(k:ℕ):completed (0:Rudder.Raw G.ColorIndex (rank r)) (stick r) (k+1)=0:=by
 obtain ⟨D,hD,h⟩:= completed_held G (k+1) (stick r) (σ:=1) zero_lt_one
 have he:= (h 0 (p:=0) le_rfl Forms.zero_held).1
 ext x; have hh:=he.plain (by positivity) (by positivity) (by omega) x; simpa using hh
end YM.RG08.Mount
