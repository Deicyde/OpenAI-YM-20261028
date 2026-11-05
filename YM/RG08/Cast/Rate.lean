import YM.RG08.Cast.Profile
import YM.RG08.Supplies.Actual

/-! # Base supply cutoff rate around the Kinetic g-scalar convention. Exact schedule
entry requirements: make σ(node)=min(kfaltpre, 1, P.α) before L; K convergence
already established after jointly asking gates; here local transfer receipts. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Cast
open Lattice Laurent Forms Pert.Bulk Isles Packets Carrel Filter Finset Function RG
open Anchor Rudder Rudder.Symmetry Exterior Stationary Bloch RG08.Flat Spar Next.Free Rows Bid Precision Loop
open scoped Topology ContDiff Classical BigOperators ENNReal Matrix
variable {G:Gauge}{T:Levels G}{H:Horizon T}{P:MapPrices}

def app (P:MapPrices)(w:ℕ→ℝ)(j:ℕ) := min (P.α j) (min 1 (w j))
lemma app_pos (P:MapPrices){w:ℕ→ℝ}(h:∀ j,0<w j):∀ j,0<app P w j:=fun j=>lt_min (P.alpha_pos _) (lt_min (by positivity) (h j))
def fees (G:Gauge)(P:MapPrices)(w:ℕ→ℝ)(h:∀ j,0<w j)(j:ℕ):ℝ := Classical.choose ((Spar.warehouse _ (app_pos P h j) (n:=1) (by norm_num) (Symmetry.dressed G 2) (Symmetry.respects G 2)).choose_spec) -- K after theta

def breadth (G:Gauge)(P:MapPrices)(w:ℕ→ℝ)(h:∀ j,0<w j)(j:ℕ):ℝ := Classical.choose (Spar.warehouse _ (app_pos P h j) (n:=1) (by norm_num) (Symmetry.dressed G 2) (Symmetry.respects G 2))
lemma fee (G:Gauge)(P:MapPrices){w:ℕ→ℝ}(h:∀ j,0<w j)(j:ℕ):Rigged (n:=1) (dye G) (app P w j) (breadth G P w h j) (fees G P w h j):=(Spar.warehouse _ (app_pos P h j) (n:=1) (by norm_num) (Symmetry.dressed G 2) (Symmetry.respects G 2)).choose_spec.choose_spec

-- Quorum ⇒ overlap shot on stabilizer. Layer K exponential gain & all primers consumed explicitly.
lemma stability (hΛ:∀ k,0≤Lambda' T k)(h:H.Suffices P)(hi:∀ N i n,i≤N → Sworn (H.H N i) n G){w:ℕ→ℝ}(hw:∀ j,0<w j){F:ℕ→Kernel Flat.Links Flat.Links}{A B c:ℝ}{d l a:ℕ}(hq:Quorum w F a H A B d l c) (i k N m:ℕ)(hi' : a ≤ i)(hn : i ≤ N)(hm : N ≤ m):
   let j:=T.clock.J i ; let θ:=breadth G P w hw j
   let e:=starter G (H.H N i) θ; let b:=starter G (H.H m i) θ
   let p (N:ℕ):=A*Flat.clock T.S (Lambda' T) k i^d * ((T.S.a N/T.S.a i)^c)
   ; Held (carpet _) θ (fees G P w hw j*(tax G 1*(2*p N))) (e - b):=by
  intro j θ e b p
  have Hp n:= hq.approximates k i n hi'
  let L:=w j;let U n:=Flat.output (H.H n i)
  have hf n (hi:i≤n): RowCost L 1 (U n-F i) (p n):=Hp _ hi
  have he n:0≤ p n:=by unfold p Flat.clock Lambda';have hk:=hq.logged;have ho:= T.S.a_pos i;have hj:=T.S.a_pos n;have ht:=hΛ k;unfold Lambda' at ht;positivity
  have ht:app P w j≤L := (min_le_right ..).trans (min_le_right ..)
  have ht':app P w j≤P.α j:=min_le_left ..
  have Hs n (hh:i≤n): (H.H n i).metric.strip (app P w j) (P.Ω j):=fun x y=> ((h.rows n i hh).2.1 x y).mono ht' le_rfl
  have hb:p m≤p N:=by
    unfold p
    apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by exact div_nonneg (T.S.a_pos _).le (T.S.a_pos _).le) (div_le_div_of_nonneg_right (T.S.strictAnti.antitone hm) (T.S.a_pos _).le) hq.positive.le) _
    have ha:=hΛ k;have hh:=hq.logged;unfold Flat.clock;positivity
  apply seats_diff (G:=G) _ _ (Hs _ (hn.trans hm)) (Hs _ hn) (h.all _ _ (hn.trans hm)) (h.all _ _ hn) (fun n=>hi _ _ n (hn.trans hm)) (fun n=>hi _ _ n hn) (app_pos P hw j) ((min_le_right ..).trans (min_le_left ..)) (Ω_pos h i) (fee G P hw j) _ (by have := he N; positivity)
  have Hx : RowCost (app P w j) 1 (U N-U m) (p N+p m):=by
    convert (subtract_row (hf N hn) (hf m (hn.trans hm)) (he N) (he m)).mono ht using 1
    funext x y; simp
  exact fun v z=>(Hx v z).trans (ENNReal.ofReal_le_ofReal (by linarith))
end YM.RG08.Cast
