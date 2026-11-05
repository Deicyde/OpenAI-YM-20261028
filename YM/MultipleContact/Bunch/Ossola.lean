import YM.MergeProof.North.Fram
import YM.MultipleContact.Bunch.Focal
import YM.MultipleContact.Bunch.Dew
import YM.MultipleContact.Bunch.Gush
import YM.MultipleContact.Bunch.Sugary
import YM.MultipleContact.Bunch.Stained
import YM.MultipleContact.Bunch.Stator
import YM.MultipleContact.Bunch.Wiring
import YM.MultipleContact.Bunch.Frost
import YM.MultipleContact.Bunch.Fermi
import YM.MultipleContact.Bunch.Corn
import YM.MultipleContact.Bunch.Lyme
import YM.MultipleContact.Bunch.Botan
import YM.MultipleContact.Bunch.Junction
import YM.MultipleContact.Bunch.Nigella
import YM.MultipleContact.Bunch.Buoy
import YM.MultipleContact.Bunch.Gild
import YM.MultipleContact.Bunch.Farr
import YM.MultipleContact.Bunch.Billow
import YM.MultipleContact.Bunch.Blot
import YM.MultipleContact.Bunch.Pond
import YM.MultipleContact.Bunch.Shan
import YM.MultipleContact.Bunch.SkyFall
import YM.MultipleContact.Bunch.Quark
import YM.MultipleContact.Bunch.Menu
import YM.MultipleContact.Bunch.Wraith
import YM.MultipleContact.Bunch.Thumb
import YM.MultipleContact.Bunch.Arbor
import YM.MultipleContact.Bunch.Platform
import YM.MultipleContact.Bunch.Islands
import YM.MultipleContact.Bunch.Quiet
import YM.MultipleContact.Bunch.Price
import YM.MultipleContact.Bunch.Antique
import YM.MultipleContact.Bunch.Apiary
import YM.MultipleContact.Bunch.Stable
import YM.MultipleContact.Bunch.Belvedere
import YM.MultipleContact.Bunch.Thunder
import YM.MultipleContact.Bunch.Muscat
import YM.MultipleContact.Bunch.Fram

/- generalized from YM.MergeProof.North.Ossola to arbitrary arity -/
/-! Off launch fixed cut.W.Concrete rep.exe -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.MergeProof.BatchRibbons
variable {slot:Type}[Fintype slot][DecidableEq slot][Inhabited slot]
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent BatchRibbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
section
variable {V : Type}[Fintype V][DecidableEq V]{G:Gauge}(H:History G) {N m p k:ℕ}(δ:ℕ→ℝ)(r:ℕ→ℕ)
    (D:∀ N p m:ℕ,m<N→GaugeDoor (H.rep N p (m+1)) (H.rep N p m))
variable (E:∀ m:ℕ,V→Site (H.S.side m p))(o:∀ m:ℕ,Name V slot→Site (H.S.side m p))(P:V→ Motion)(v:V)(w:slot→ℝ)(B:V→Equiv.Perm V)
set_option quotPrecheck false
local notation "Ξ"=> (Aged V slot)
local notation "P'"=> H.levels.budget
local notation "R"=> H.rep N p
local notation "Q"=> R N
local notation "L'"=> (fun m=> ((H.S.block m).val:ℝ))
local notation "x"=> (fun m=> 6*L' m)
variable {l:Name V slot→ℂ}(σ χ:ℕ→ℝ){μ j:ℕ}
    {S:∀ m:ℕ,m≤N→ Config G (H.S.side m p)→Poly (Aged V slot)}
    (h:H.Selected) (hr:Thor (slot:=slot) H δ r D σ χ μ)(ht':μ≤k)(hQ: Migrating H k p N E)
    (hΔ: ∀ m:ℕ, k ≤ m→∀ hm:m<N, S m hm.le=(H.levels.clock.op m p).push ((H.rep N p (m+1)).beta) (S (m+1) hm))
    (hp:∀ m:ℕ,k ≤ m→∀ hm:m≤N,Integrable (S m hm) (prior G _))
    (hO:∀ m:ℕ, k ≤ m→m≤j→∀ i,i≠v→∀ b:slot,o m (i,b)=affine (P i).1 (E m i) (o m (v,b)))
def krill (T:Schedule) (j i:ℕ)(b:ℝ):=b/16*(T.a j/T.a i)^4
local notation "ω"=> (fun i (a:slot)=>krill H.S j i (w a))
local notation "W"=> (fun i (a:Name V slot)=> ω i a.2)
variable (hN:j≤N)(hY:∀ m:ℕ,k ≤ m→∀ hi:m<j, MergeProof.Float.Runs (D N p m (hi.trans_le hN)) (H.levels.clock.op m p) (6*((H.S.block m).val:ℝ)))
include hY hN h hr ht' hQ hΔ hp hO
lemma ossuary (hk:k<j)(F K t)(hU:Arc (R j) F K (S j hN) v P (E j) B (o j) (fun i=>w i.2) ((P' j).supportExponent+1/2) ((P' j).supportExponent+1) 1 (χ j) t l) (he:∀ i,i≠v→∀ b:slot,l (i,b)=scalar (P i) (l (v,b))) (hw:∀ i,0< w i) (hw':∀ i:Name V slot,w i.2*‖l i‖ ≤ 1) (hξ:χ j≤1)(hD:Arsenal (R j))(hL:∀ i,k ≤ i→i<j→2 ≤ L' i)(φ:ℕ→ℝ)(hF:Brine H k δ φ)(hC:∀ i,k ≤ i →i<j→φ i≤1)(hP:∀ m:ℕ,k ≤ m→m≤j→Drake Ξ (P' m).B (o m))(hM:Monotone r)(hz:Occupancy (o k) (r k))(ht:∀ m:ℕ,k ≤ m→m<j→(H.levels.clock.op m p).ratio.parent ∘ o (m+1)=o m):∃ g L, Arc (R k) g L (S k (hk.le.trans hN)) v P (E k) B (o k) (fun i=>δ k *W (k+1) i) ((P' k).supportExponent+1/2) ((P' k).supportExponent+1) 1 (χ k) (δ k) l ∧ ∀ i, δ k*W (k+1) i * ‖l i‖≤1:=by
    have hV(i)(b:slot): 0<ω i b:= mul_pos (div_pos (hw _) (by norm_num)) (pow_pos (div_pos (H.S.a_pos _) (H.S.a_pos _)) _)
    have hX0(i:ℕ)(he:k ≤ i)(hm:i<j):1 ≤ x i:= by change (1:ℝ) ≤ 6*L' i; linarith only [hL _ he hm]
    have hA(i:ℕ)(he:k ≤ i)(hm:i<j)(b:slot):x i*ω i b ≤ ω (i+1) b:=by
       have hx:L' i ^ 3 ≥ 8:= by have hh:=pow_le_pow_left₀ zero_le_two (hL i he hm) 3;norm_num at hh ⊢; exact hh
       have hv': H.S.a i=H.S.a (i+1)*L' i:=(H.S.embeds_scale (H.S.oneStep i p)).symm
       have hh:ω (i+1) b=L' i ^4 *ω i b:=by
           unfold krill; dsimp only; rw [hv']; have he':=H.S.a_pos (i+1); have hi:0<L' i:=zero_lt_two.trans_le (hL i he hm); field_simp
       rw [hh]; refine mul_le_mul_of_nonneg_right ?_ (hV _ _|>.le)
       rw [pow_succ]; exact mul_le_mul_of_nonneg_right (by linarith only [hx]) (zero_le_two.trans (hL _ he hm))
    have hy(i:ℕ)(he:k ≤ i)(hm:i<j)(b:slot):ω i b ≤ ω (i+1) b:= (le_mul_of_one_le_left (hV i b|>.le) (hX0 i he hm)).trans (hA i he hm b)
    have hc(b): 8 * ω j b ≤ w b:=by unfold krill;dsimp only; rw [div_self (H.S.a_pos _).ne',one_pow,mul_one]; linarith only [hw b]
    have ht':Matchup H r δ p j k o W Ξ:=by
       have hε:∀ m:ℕ,k ≤ m→m≤j → Occupancy (o m) (r k):=by
          intro m he hp; induction he with
          | refl =>exact hz
          | step hi ih=>rename_i i; intro b; let f:=(H.levels.clock.op i p).ratio
                        have hρ:= ih (show i ≤ j by omega) (f.parent b); apply le_trans (Finset.card_le_card _) hρ
                        intro a h; refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩; rw [← ht _ hi hp];simp only [Function.comp_apply]; exact congr_arg f.parent (Finset.mem_filter.mp h).2
       refine ⟨fun i h p j=>hV i _,fun i he hp j=> (hε i he hp j).trans (hM he),fun i he hp j=> (hε (i+1) (he.trans i.le_succ) hp j).trans (hM he),ht,fun i he hm=> ?_⟩
       apply (hP i he hm.le).palms _ (fun j=>hV i _) (fun j=> mul_pos (hF.water i he).2 (hV (i+1) j.2)) (hF.support i he); intro z
       have hZ:= hF.mint i he; let c:= mintK (P' i).B; have ht': 1 ≤ δ i*c:= by exact hZ.trans (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (hF.water i he).2.le (hC i he hm)) (show 0 ≤ mintK (P' i).B from (Real.exp_pos _).le))
       exact (hy i he hm z.snd).trans ((le_mul_of_one_le_right (hV (i+1) z.snd|>.le) ht').trans_eq (by ring))
    obtain ⟨g,L,hZ⟩:= framing H δ r D E o P v ω B σ χ h hr ‹μ ≤ k› hQ hΔ hp ht' hO x hN hY (fun i he hm=>zero_le_one.trans (hX0 _ he hm)) hA hk F K t w hU he hξ hc hD
    refine ⟨g,L,hZ,fun b=>?_⟩
    have hx':∀ i,k ≤ i→i≤j→ω i b.2 ≤ w b.2:=by
       intro m hi hm; induction hm using Nat.decreasingInduction with
       | self=> linarith only [hV j b.2,hc b.2]
       | of_succ i hj IH=> exact (hy i hi hj _).trans (IH (hi.trans i.le_succ))
    exact (mul_le_mul_of_nonneg_right ((mul_le_of_le_one_left (hV (k+1) b.2|>.le) (hr.suns k ‹μ ≤ k›).hats.2).trans (hx' _ k.le_succ hk)) (norm_nonneg _)).trans (hw' b)
end
end YM.MergeProof.BatchRibbons
