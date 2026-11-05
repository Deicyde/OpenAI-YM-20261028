import YM.RG08.Carrel.Hood
import YM.RG08.Spar.Align

/-!
# Complete unmarked packets at all ranks and compare all their positive rescaled evaluations
with finite path jets. (At rank 0 slots of later coupling degree, USE NONE; conventions
apply for n, all valences >0 only.) Results at each period and cover cofinal. Read all atoms
evaluated before masks and BEFORE tree conditioning. Entry to perturbed conditional calculation
uses these, and correct change of variables and log reexpression etc.)
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Carrel
open Lattice Laurent Forms Pert.Bulk Isles Packets Rudder Rudder.Symmetry Filter Finset Function RG Extra.Iteration
open Camera Cloud Room Glyph Exterior Wilson Precision Spar
open scoped BigOperators Topology Classical ENNReal PowerSeries Matrix
variable {G:Gauge}{k n:ℕ}{P:Side}

def completed (F:Rudder.Raw G.ColorIndex n)(o:Fin n)(k:ℕ):Flake k (Market (Rayk G 1)):=bleach (Carrel.average (grown (mass (deposit (Anchor.compress 2 F) o) k)))

-- always provide positive-rank arity, σ taken for F and all powers. same degree read for base too.
theorem completed_held (G:Gauge)(k:ℕ)(o:Fin n){σ:ℝ}(hσ:0<σ):
 ∃ D:ℝ,0≤D∧∀ (F:Rudder.Raw G.ColorIndex n){p:ℝ}, 0≤p→Held (carpet _) σ p F →
    Held (carpet _) (σ/n/32) (D*p) (completed F o k) ∧
    -- H & sym output
    Sym (completed F o k) ∧ Cohort (completed F o k):=by
 let C:=Fintype.card (Rayk G 2);let η:=σ/(n:ℝ)
 obtain ⟨A,hA,h⟩:=fare G n k (show 0<η from div_pos hσ (Nat.cast_pos.mpr o.pos))
 let V:= Real.exp (η*(4*n:ℕ)) * (C:ℝ)
 let D:=V*A*Real.exp (8*(η/32))
 have hV:0≤V:=by unfold V;positivity
 refine ⟨D,by unfold D;positivity,fun F {p} hp H=> ⟨?_,symmetric _,(average_cohort (grown_y _)).clean⟩⟩
 let Q:=Anchor.compress 2 F
 have ht:= (h (paid Q o hσ hp (Anchor.compress_cost 2 H))).1
 have hy:0 ≤ V*p*A:=by positivity
 convert (average_held (grown (mass (deposit Q o) k)) ht (by unfold η; positivity) hy).bleach (by exact mul_nonneg hy (by positivity)) using 1
 unfold D V η at *
 ring
 rfl

variable {F:Rudder.Raw G.ColorIndex n}{σ p:ℝ}

theorem hatch (o:Fin n)(_h:Cohort F)(H:Held (carpet _) σ p F)(ht:0<σ)(hp:0≤p)(i:Fin k)(u:Vert P (Rayk G 1)):
 let M:=deposit (Anchor.compress 2 F) o
     ; reading (pour (completed F o k) i) u=(Fintype.card Signed:ℝ)⁻¹ * ∑ s:Signed, ∑' z,∑ l:Site P, MvPolynomial.eval (treated s u) (tap k (flask (showAtom (M z) l))) :=by
 dsimp only
 let Q:=Anchor.compress 2 F;let M:=deposit Q o
 let η:=σ/(n:ℝ)
 have hy:0<η:=div_pos ht (Nat.cast_pos.mpr o.pos)
 obtain ⟨A,hA,h⟩:=fare G n k hy
 have hh:= h (paid Q o ht hp (Anchor.compress_cost 2 H));rw [completed,interested _ (grown_y _) hh.1 (by positivity)]
 congr 1;apply Finset.sum_congr rfl;intro s _; exact hh.2 P i (treated s u)

lemma curl_read (F:Rudder.Raw G.ColorIndex n)(o:Fin n)(h:Cohort F)(he:Held (carpet _) σ p F)(hp:0≤p)(ht:0<σ)(u:Vert P (Rayk G 1)):
    reading (pour (Anchor.compress 1 (picture G.ColorIndex n F)) o) u=reading (pour (Anchor.compress 2 F) o) (curling G u):=by
 rw [descend o (NextTo.unit ht hp h he o.pos)]
 let M:=shaded P P G.ColorIndex ((cobound 1).acts P)
 unfold reading query
 simp_rw [Finset.sum_mul];rw [Finset.sum_comm];apply Finset.sum_congr rfl;intro i _
 simp_rw [mul_assoc,←Finset.mul_sum,←Finset.prod_mul_distrib]
 rw [← Fintype.prod_sum (f:=fun (k:Fin n)y=> M (i k) y*u y)]
 apply congrArg₂ (·*·) rfl;apply Finset.prod_congr rfl;intro k _
 rcases h:(i k) with ⟨x,r,b⟩
 -- expand dColor
 unfold curling Exterior.dColor directors Exterior.parts
 change (∑ y:Cove P (Rayk G 1), M (x,r,b) y*u y)= Matrix.mulVec (d 1 P) _ (x,r)
 simp_rw [Fintype.sum_prod_type]
 unfold M Spar.shaded Matrix.mulVec dotProduct; simp_rw [Fintype.sum_prod_type]
 simp [ite_mul];rfl

-- orbit rigor for leading unmasked read
lemma emerged (o:Fin n)(h:Cohort F)(H:Held (carpet _) σ p F)(ht:0<σ)(hp:0≤p)
   (same : ∀ s:Signed,adjust s (Anchor.compress 1 (picture G.ColorIndex n F))=Anchor.compress 1 (picture _ _ F))
   (u:Vert P (Rayk G 1)):
    reading (pour (completed F o n) o) u=reading (pour (Anchor.compress 1 (picture G.ColorIndex n F)) o) u:=by
 let Q:=Anchor.compress 2 F;let Y:=Anchor.compress 1 (picture G.ColorIndex n F)
 let η:=σ/(n:ℝ);have hy:0<η:=div_pos ht (Nat.cast_pos.mpr o.pos)
 obtain ⟨A,hA,ha⟩:=fare G n n hy
 have hm:=ha (paid Q o ht hp (Anchor.compress_cost 2 H))|>.1
 rw [completed,interested _ (grown_y _) hm (by positivity)]
 have he:Y=Y:=rfl
 have hv(s:Signed): reading (pour (grown (mass (deposit Q o) n)) o) (treated s u)=reading (pour Y o) u:=by
   have hh:=led o (Anchor.compress_path 2 h) (Anchor.compress_cost 2 H) ht hp (treated s u)
   change reading _ _=reading _ _
   rw [show reading (pour (grown (mass (deposit Q o) n)) o) (treated s u)= reading (pour Q o) (curling G (treated s u)) from hh,←curl_read F o h H hp ht,←according s (Anchor.compress_path _ (NextTo.cohort (Spar.photograph (NextTo.unit ht hp h H o.pos)))) o u,same]
 change (Fintype.card Signed:ℝ)⁻¹ * (∑ s,reading (pour (grown (mass (deposit Q o) n)) o) (treated s u))=_
 rw [Finset.sum_congr rfl (fun s _=>hv s)]; simp; rfl

theorem spared (o:Fin n)(h:Cohort F)(H:Held (carpet _) σ p F)(ht:0<σ)(hp:0≤p)(i:Fin k)(hi:k<n)(u:Vert P (Rayk G 1)):
 reading (pour (completed F o k) i) u=0:=by
 rw [hatch _ h H ht hp];simp_rw [before_first _ _ _ hi,map_zero];simp

end YM.RG08.Carrel
