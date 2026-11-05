import YM.RG08.Aggregate.Spice
import YM.RG08.Crown.Cost

/-!
# FPS evaluation of completed invariant path template at any finite regulator,
   stable under rescaled formal transformations. kth coefficient transfer to
   access unmatched Ward identity later across tori. Also accounts for n=0 at
   this analytic germ stage. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Aggregate
open Carrel Camera Room Cloud Glyph Lattice Laurent Function Finset Filter
open RG Wilson Forms Isles Pert.Bulk Rudder Symmetry Anchor MvPolynomial
open scoped BigOperators Topology ENNReal PowerSeries Classical ContDiff
variable {I:Type}{G:YM.Gauge}{n k:ℕ}{P:Side}

-- version of hatch with HasSum accounting: infinite template constituents evaluated in
-- all sign channels on actual log Taylor expansion.
variable {F:Rudder.Raw G.ColorIndex n}{σ p:ℝ}

def atoms (F:Rudder.Raw G.ColorIndex n)(i:Fin n)(j:Coord (n:=n))(s:Signed)(o : Site P) : Still (Bedge G P):=showAtom (deposit (compress 2 F) i j) o ∘ Crown.turns s
def annulus (F:Rudder.Raw G.ColorIndex n)(i:Fin n)(P:Side)(j:Coord (n:=n)):Port (Bedge G P):=(Fintype.card Signed:ℝ)⁻¹ • ∑ s:Signed,∑ o:Site P,flask (atoms F i j s o)
-- include 0 arity =0 from n>0

def component (F:Rudder.Raw G.ColorIndex n)(i:Fin n)(P:Side)(k:ℕ):Inn (Bedge G P):= if h:0<k then parley (pour (completed F i k) ⟨0,h⟩) else 0
def booked (F:Rudder.Raw G.ColorIndex n)(i:Fin n)(P:Side):Port (Bedge G P):=PowerSeries.mk (component F i P)

lemma atom_pace (o:Fin n)(j:Coord (n:=n))(s:Signed)(w:Site P):Camera.Pace (atoms F o j s w):=by
 obtain ⟨C,hC,H⟩:=per_atom G n 0 (η:=1) (by norm_num)
 unfold atoms;refine ContDiffAt.comp _ ?_ (Crown.turns s).contDiff.contDiffAt
 rw [map_zero];exact (H (deposit (compress 2 F) o j) _ w).analytic

lemma fit (i:Fin n){j:Coord (n:=n)}(s:Signed)(v:Vert P (Rayk G 1))(o:Site P)(k:ℕ):
 MvPolynomial.eval v (tap k (flask (atoms F i j s o)))=MvPolynomial.eval (treated s v) (tap k (flask (showAtom (deposit (compress 2 F) i j) o))):=by
 obtain ⟨C,hC,H⟩:= per_atom G n 0 (by positivity : 0<(1:ℝ)); exact (Crown.switch (show Camera.Pace (showAtom (deposit (compress 2 F) i j) o) from (H ..).analytic) s k v).symm

theorem recipe {P:Side}(h:Cohort F)(he:Held (carpet _) σ p F)(hp:0≤p)(hs:0<σ)(i:Fin n)(k:ℕ):Along (Coord (n:=n)) (fun j=>tap k (annulus F i P j)) (tap k (booked F i P)):=by
 intro x
 let a (j:Coord (n:=n)):=Carrel.deposit (compress 2 F) i j
 change HasSum (fun j=> MvPolynomial.eval x (tap k (_ • ∑ s:Signed,∑ o:Site P,_))) (MvPolynomial.eval x (tap k (PowerSeries.mk _ : Port (Bedge G P))))
 let U(j:Coord (n:=n))(s:Signed):= ∑ o:Site P, MvPolynomial.eval (treated s x) (tap k (flask (showAtom (a j) o)))
 have hy (s:Signed):Summable (fun j: Coord (n:=n)=>U j s):=by
    have H:=paid (compress 2 F) i hs hp (compress_cost _ he)
    obtain ⟨D,hD,H'⟩:=fleet G n k (σ:=σ/(n:ℝ)) (div_pos hs (Nat.cast_pos.mpr i.pos))
    have hh:= H' H
    have ht(w:Site P):Summable (fun t:Coord (n:=n)×Slide (Rayk G 1) k=>stored (a t.1) k t.2 *per_use t.2 (treated s x) w):=hh.uses (by positivity) _ w
    unfold U; simp_rw [stored_view];exact summable_sum fun v _=> (ht v).prod
 by_cases hi:0<k
 · have hm:= hatch i h he hs hp (Fin.mk 0 hi) x
   change reading (pour (P:=P) (completed F i k) ⟨0,hi⟩) x=_ at hm
   rw [show tap k (PowerSeries.mk _ :Port (Bedge G P))=component F i P k from PowerSeries.coeff_mk ..,component,dif_pos hi,←reading_parley,hm]
   let g:ℝ:=(Fintype.card Signed:ℝ)⁻¹
   convert ((hasSum_sum (s:=univ) (f:=fun (s:Signed) (j:Coord (n:=n))=>U j s) (fun s _=> (hy s).hasSum)).const_smul g) using 1
   funext b;simp only [tap,PowerSeries.coeff_smul,map_sum,← MvPolynomial.aeval_eq_eval,_root_.map_smul,smul_eq_mul];change _=(Fintype.card Signed:ℝ)⁻¹*_
   apply congrArg₂ (·*·) rfl
   apply Finset.sum_congr rfl;intro s _;apply Finset.sum_congr rfl;intro v _;exact fit ..
   rfl
 · obtain rfl:k=0:=by omega
   have hv (j:Coord (n:=n))(s:Signed)(q:Site P):atoms F i j s q 0=0:=by
      unfold atoms;rw [Function.comp_apply,map_zero]
      have H : MvPolynomial.eval x (tap 0 (flask (showAtom (a j) q)))=0:=by rw [before_first (a j) q 0 i.pos];exact map_zero _
      simpa [tap,flask,print,a] using H
   simp [tap,map_sum,PowerSeries.coeff_mk,component,flask,print,hv]

lemma booked_lane (F:Rudder.Raw G.ColorIndex n)(i:Fin n)(P:Side)(k:ℕ):tap k (booked F i P)∈ Lane (Bedge G P) k:=by
 rw [booked,tap,PowerSeries.coeff_mk,component];split;· exact lane_in _
 exact zero_mem _
lemma ann_lane (F:Rudder.Raw G.ColorIndex n)(i:Fin n)(P:Side)(k:ℕ)(j):tap k (annulus F i P j)∈ Lane (Bedge G P) k:=by rw [annulus,tap,PowerSeries.coeff_smul,map_sum];simp_rw [map_sum];apply (Lane _ _).smul_mem;apply sum_mem;intro y _; apply sum_mem;intro o _; apply lane_photograph

theorem driven {P:Side}(h:Cohort F)(he:Held (carpet _) σ p F)(hp:0≤p)(hs:0<σ)(i:Fin n)(e:ℕ)(x:Bedge G P→Port I):
 Along (Coord (n:=n)) (fun j=>tap e (belt x (annulus F i P j))) (tap e (belt x (booked F i P))):= sweep id e (fun k _=>recipe h he hp hs i k) (fun _ _ _=>ann_lane ..) (fun _ _=>booked_lane ..) _
end YM.RG08.Aggregate
