import YM.MultipleContact.Multi.Store

/-! Uniform profiles of field insertions and comparable signed products in separated collars. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.MultipleContact.Centered
open Filter Set Function MeasureTheory Extraction Spec Table Script Scene Drama ScheduleRow Bunching
open MergeProof RG
open scoped Classical Topology BigOperators

variable {G:Gauge}{L:Register G}(S:Table L)

/-- `anchor` designates anchored, `root` arbitrary relative center. -/
inductive March
 | raw
 | anchor (h:ℕ) (D:Detector S h)
 | root (h:ℕ) (D:Detector S h)
 | field (h:ℕ)
namespace March
variable {S} (g:March S)
abbrev Data : Type _ := match g with
 | .field h=> S.Field h
 | _ => Unit
noncomputable instance : Inhabited (Data g):= by cases g <;> first | exact ⟨(0:S.Field _)⟩ | exact ⟨()⟩
variable {n:ℕ}
def payload (v:Fin n→ S.Tag) (z:E4)(x:Fin n→E4)(q:g.Data): Grammar (Alpha S):=
        match g,q with
        | .raw, _=> Scene.packet S v x z
        | .anchor h D, _ => Scene.residue S D v x z
        | .root h D, _=> Scene.residue S D v x z
        | .field h,v=>insertion S z v
def weight (v:Fin n → S.Tag)(ε:ℝ):ℝ:=match g with
 | .raw=>-(massOf v:ℝ)-ε
 | .anchor h _ => -(massOf v:ℝ)+h+1/64
 | .root h _=> -(massOf v:ℝ)+h+1/64
 | .field _ =>0
def load(q:g.Data):ℝ:=match g,q with | .field h,v=>max 1 ‖(show S.Field h from v)‖ | _,_=>1
-- syntax: point configuration centered at z, separately supplied in payload. `allow` on relative positions.
def allow [Inhabited (Fin n)] (N:Lattice.Side)(ρ:ℝ)(x:Fin n→ E4):Prop:=match g with
 | .field _=> True
 | _=> (∀ i j:Fin n,i≠j→ρ/4<‖x i-x j‖) ∧ (∀i,‖x i‖<2*N.val*ρ) ∧ (∀ h (D:Detector S h),g=.anchor h D→x default=0)

def credit (v:Fin n→S.Tag)(ε ρ:ℝ)(w:g.Data):=ρ^(g.weight v ε)*(g.load w)
lemma load_pos (q:g.Data):0 < g.load q:=by cases g <;> first | exact zero_lt_one | exact zero_lt_one.trans_le (le_max_left 1 _)
lemma credit_pos (v:Fin n→ S.Tag)(ε ρ:ℝ)(q:g.Data)(h:0<ρ):0<g.credit v ε ρ q:=mul_pos (Real.rpow_pos_of_pos h _) (g.load_pos q)
end March

variable {S}{b:ℕ}{n:Fin b → ℕ} [hn:∀i:Fin b,Inhabited (Fin (n i))] (p:Fin b→March S)(V:∀i:Fin b,Fin (n i)→ S.Tag)

def Permit (κ r:ℝ)(N:Lattice.Side)(ρ:Fin b → ℝ)(z:Fin b→ E4)(x:∀i:Fin b,Fin (n i)→ E4):Prop:= Joins.Close z κ ∧ (∀i,0<ρ i ∧ ρ i < r) ∧ ∀i,(p i).allow N (ρ i) (x i)
def plainLoad {b:ℕ}{n:Fin b→ℕ}(p:Fin b → March S)(V:∀i:Fin b,Fin (n i)→ S.Tag)(ε:ℝ)(ρ:Fin b→ℝ)(q:∀i:Fin b,(p i).Data):= ∏ i:Fin b,(p i).credit (V i) ε (ρ i) (q i)
def work {b:ℕ}{n:Fin b→ℕ}(p:Fin b →March S)(V:∀i:Fin b,Fin (n i)→ S.Tag)(z:Fin b→ E4)(x:∀i:Fin b,Fin (n i)→E4)(q:∀i:Fin b,(p i).Data):= ∏ i:Fin b,(p i).payload (V i) (z i) (x i) (q i)

def Price (ε κ:ℝ) (N:Lattice.Side):Prop:=∃ A> (0:ℝ), ∃ r> (0:ℝ), ∀ (q:∀i,(p i).Data)(ρ:Fin b→ℝ)(z:Fin b→ E4)(x:∀i:Fin b,Fin (n i)→ E4), Permit p κ r N ρ z x → ‖evaluation S (work p V z x q)‖≤ A * plainLoad p V ε ρ q

def March.advanced(g:March S):Bool:=match g with | .root ..=>true | _=>false
def amount(p:Fin b→March S):= (Finset.univ.filter fun i=>(p i).advanced).card
def Good (k:ℕ)(S:Table L):Prop:=∀ {b:ℕ}{n:Fin b→ℕ} [hn:∀i:Fin b,Inhabited (Fin (n i))] (p:Fin b→March S)(V:∀i:Fin b,Fin (n i)→S.Tag)(ε κ:ℝ)(N:Lattice.Side),0<ε→0<κ→amount p≤k → Price p V ε κ N
end YM.MultipleContact.Centered
