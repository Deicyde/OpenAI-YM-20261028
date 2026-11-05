import YM.RG08.Rudder.Pin

/-!
# General linear choice for χ-before-length quasi-local lifts on the cover
-/
noncomputable section
namespace YM.RG08.Rudder
open scoped lp Topology BigOperators Classical ENNReal
open Forms Packets Finset Function Lattice Pert.Bulk
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I:Type}{n r:ℕ}

abbrev Paint (I:Type)(n:ℕ):=Flake n (Market I)
/-- Consume system L of literal stencil identities. Continuous in pointwise topology
(e.g. polynomial-external Ward at fixed local link). If extra ranks are required to vanish
put *that* also into L. `L` needn't commute with translations: cohere promised separately.
-/
def answer (i:Fin n)(θ:ℝ)(L:Paint I n→L[ℝ] Paint I r) : Paint I r→ Paint I n:=fun x=> caddy i θ (Trial.reply (L.comp (caddy i θ)) x)

variable [Fintype I]{θ T:ℝ}{i:Fin n}{L:Paint I n→L[ℝ] Paint I r}

structure Possible (i:Fin n)(θ:ℝ)(L:Paint I n→L[ℝ] Paint I r)(T:ℝ)(F:Paint I r):Prop where
 rate : 0<θ
 cost : 0≤T
 get : ∃ X, L X=F ∧ Cohort X ∧ Held (carpet I) θ T X

variable {F G:Paint I r}

private lemma shelf (h:Possible i θ L T F):∃ f:Shelf I i,L (caddy i θ f)=F ∧ ‖f‖≤Fintype.card I*T:=by
 obtain ⟨X,hx,H,hP⟩:=h.get
 obtain ⟨f,hh,hf⟩:=loads (i:=i) H hP h.cost
 exact ⟨f,hh ▸ hx,hf⟩ -- hh : caddy ..=X

theorem pays (h:Possible i θ L T F): L (answer i θ L F)=F ∧ Cohort (answer i θ L F) ∧ Held (carpet I) (θ/2) ((debit' I n θ*(2*Fintype.card I))*T) (answer i θ L F):=by
 obtain ⟨f,hf,he⟩:=shelf h
 refine ⟨Trial.solves (L.comp (caddy i θ)) F hf, caddy_cohort _,?_⟩
 rw [mul_assoc]
 apply regain (Fin.pos i) h.rate (by have he:=h.cost;positivity)
 intro x
 apply (caddy_point ..).trans
 apply (Trial.spend (L.comp (caddy i θ)) F hf).trans
 linarith

theorem stable {C D:ℝ}(h:Possible i θ L C F)(h':Possible i θ L D G):answer i θ L (F-G)=answer i θ L F-answer i θ L G:=by
 unfold answer; rw [Trial.subtract,map_sub] <;> first | (obtain ⟨v,hv,-⟩:=shelf h;exact ⟨v,hv⟩) | (obtain ⟨v,hv,-⟩:=shelf h';exact ⟨v,hv⟩)
end YM.RG08.Rudder
