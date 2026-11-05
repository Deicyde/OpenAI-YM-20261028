import YM.MergeProof.West.Karin
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Relation Finset Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
open MeasureTheory Cells Edition
variable {G:Gauge}{N n p k q i d D:ℕ} {C:Family G} {R:Lead G C.S p}
   {b:ℝ} {c:Course C N p k}{x:Points n}{hk:i<k}{h:middle C.path.levels b k ≤ i}
   {T τ U ε g B Y L} (E:StageNow (d:=d) c R x b hk h q T τ U ε)
lemma resists (W: Fin n → poly (Chamber G C.S k p)) (hk:i≤k) (v:modes (Fin n)):
   honors (sprout (Fin n) (primeLog _) v) (vista R W hk) = heads R W hk v:= by
   apply audible; intro x; let A:=t_cum R W hk x
   have he:=expanders R W hk x
   calc
    _ = (medicine _ A).part v:= g_honors (aeval (R:=ℂ) (fun i=> (x i:ℂ))) _ _
    _ = _:= by rw [diaper,infancy]; exact congr_arg (fun K=>Poly.part K v) he.2

variable (W: Fin n → poly (Chamber G C.S k p))
variable (hP : ∀ u,vista R W hk u ≠ 0 → ∃ i : ViewFt C k b p d x hk,i.val.val=u)
variable (hx:roomTest C.path.levels b k p d q) (t:Metal b c R hk ε τ g B Y L) (Hv:Healthy g (d_olm x b q (walls (clim C.path.levels i)) c.allow hk.le T.1 T.2.val) U) (he: 0 < ε) (he':ε≤1)
   {r:ℝ} (hr:0≤r)
variable (H:∀ u, Poetic (vista R W hk u)) (hs:∀ u,totalDegree (vista R W hk u)≤ D) (hu:∀ u,coin (vista R W hk u)≤ r) (hp:∀ u : Manner n,∀ i'∈(vista R W hk u.val).vars,spotFt b (i+1) d (show i+1≤k from hk) x u i' (C:=C))

local notation "O"=> offerNow E (vista R W hk)
def gentility (B ε r:ℝ) (D n:ℕ):= ∑ u : modes (Fin n), grantS (sprout (Fin n) (primeLog _) u) B ε r D
variable {W}
def vantage (_ : StageNow (d:=d) c R x b hk h q T τ U ε) := let D:=basisFt c x b i c.allow hk.le h T.1 T.2.val U; rigid D
variable (W)
set_option quotPrecheck false
local notation "F"=> Array.reorient (Ship.yard C b c.allow p) T.1 (spunW R W hk.le (vantage E))
include hP hx t Hv he he' hr H hs hu hp
lemma flight_pay (v:modes (Fin n)) (hv:v.val ⊆ T.2.val.val.val) : ‖(planterFt E (offerNow E (vista R W hk))).part v-(F).part v‖ ≤ gentility B ε r D n:=by
  let Y:=sprout (Fin n) (primeLog _) v
  have hx (j : Fin E.count) (z) : (Poly.pass (p_lanter E (offerNow E (vista R W hk)) j z)).part v=tray E Y (vista R W hk) j z:= by
     let V:=p_lanter E (offerNow E (vista R W hk)) j z; change (Poly.pass V).part v= (medicine (sprout _ (primeLog _)) V).part v; rw [diaper,infancy]
  have ht:(planterFt E (offerNow E (vista R W hk))).part v=plaidFt E (tray E Y (vista R W hk)):=congr_arg (plaidFt E) (funext fun i=>funext fun j=> hx i j)
  rw [ht]
  let Z := vantage E
  have hf : (F).part v= dot ((Ship.yard C b c.allow p).hand T.1) (text Z (heads R W hk.le v)):= by dsimp only [Array.reorient,Edition.dot];split_ifs <;> rfl
  rw [show (F).part v=platter (T:=T) (R:=R) (c:=c) (hk:=hk) (h:=h) (U:=U) Y (vista R W hk) by rw [hf,platter,resists,show heads R W hk.le v=_ from shelving R hk _]; rfl]
  apply (sweep E Y (vista R W hk) hP ‹roomTest _ _ _ _ _ _› t Hv he he' hr H hs hu hp (fun w h j hj=> (embraces.prime.knees v w h j hj).trans hv)).2.trans
  exact Finset.single_le_sum (fun u _=> grantS_nn (sprout (Fin n) (primeLog _) u) _ _ _ D t.grain he.le hr) (Finset.mem_univ v)

end YM.Next.Rank.Tapes.West
