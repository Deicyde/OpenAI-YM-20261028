import YM.RG08.Necks.Elect
/-! # Single interval graph registration: Lag and compensated columns, at all coupling orders
 includes when no quantitative estimates supplied at higher orders.
- assembly approach: admit single-precision warm streams with fixed widths, Enough to price
 finite portion & leading matrix, then invert all orders then price finite output. Quantitative
 propagation does not need an all-orders schedule. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Sideshow
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Room Filter Laurent RG Precision Exterior Skiff Trickle Weald Hatch Carrel Quarry Steam
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Flint Lagoon Yurt Next.Free Atrium Trill Necks
open scoped Classical ContDiff BigOperators Topology ENNReal PowerSeries Matrix
variable {G:Gauge}{n D d p l e k c j t:ℕ}{σ τ μ V Q B C δ η a b W:ℝ}{P:Patch}{K:KernelChoices}
local notation "E"=> Ed G Cover
-- admission = supplies. eTarget=precision & h=d. same across slots. KERNEL booth Pair. κ axes before. V color. 
structure Font (d D k j t:ℕ)(σ τ η μ V:ℝ):Prop where
 hired (l e n:ℕ) : l≤d → e≤k → n≤l+e →Novice σ τ η μ V d D l e n j t
lemma Font.fine (h:Font d D k j t σ τ η μ V) :0<σ:=(h.hired 0 0 0 (by omega) (by omega) le_rfl).paid
lemma Font.coarse (h:Font d D k j t σ τ η μ V) :0<η:=(h.hired 0 0 0 (by omega) (by omega) le_rfl).out'

variable (X:Labels.Frame G d)
local notation "O"=> Accent X
local notation "Bh"=> Bouquet X
local notation "M"=>Playbook X

def Deck (D k:ℕ)(h:0<σ)(S:Bh):Prop:=∀ i:O,∀ e≤k,∀ j,∃ C:ℝ,0≤C ∧ Sings (stance (Loc G 1)) D h (S i e j) C
-- for Pairs always require strictly positive δ; one-order applications can self-fit via any Δ>0.
lemma deckAll {Y Y':Bh}{h:0<σ}(hs:Deck X D k h Y)(hs':Deck X D k h Y')(he:Threads D Y)(he':Threads D Y'){δ:ℝ}(hδ:0<δ)(i:O)(e:ℕ)(h₀:e≤k):
 ∃ B:ℝ, ∀ n≤octave i+e,Dyad (stance _) D h B δ (Y i e n) (Y' i e n):=by
 let I:=Fin (octave i+e+1)
 choose c hc hC using fun n:I=>hs i _ h₀ n
 choose t ht H using fun n:I=>hs' i _ h₀ n
 let A:=∑ n:I,(c n + t n);have ha:0 ≤ A:= Finset.sum_nonneg fun n _=>add_nonneg (hc _) (ht _)
 refine ⟨A+(A/δ),fun n hn=>?_⟩
 let k':I:=⟨n,by omega⟩;have hB: c k'+t k'≤A:=single_le_sum (s:=univ) (f:=fun j:I=>c j+t j) (fun j _=>add_nonneg (hc j) (ht j)) (mem_univ k')
 have hv:A ≤ A+A/δ:=le_add_of_nonneg_right (by positivity)
 refine ⟨ha.trans hv,hδ.le,⟨(he i|>.inlet.price _ _).1,(he' i|>.inlet.price _ _).1⟩,(hC k').mono le_rfl le_rfl (fun _=>le_rfl) (le_trans (le_add_of_nonneg_right (ht _)) (hB.trans hv)),(H k').mono le_rfl le_rfl (fun _=>le_rfl) (le_trans (le_add_of_nonneg_left (hc _)) (hB.trans hv)),((hC k').sub (H k') (hc _) (ht _)).mono le_rfl le_rfl (fun _=>le_rfl) (hB.trans ?_)⟩
 rw [add_mul,div_mul_cancel₀ _ hδ.ne'];exact le_add_of_nonneg_left (mul_nonneg ha hδ.le)

lemma deckFusion {Y:Bh}{h:0<σ}(hs:Deck X D k h Y)(N:M):Deck X D k h (Atrium.shuffle N Y):=by
 intro i e he n
 choose c hC H using fun t:O×Fin (e+1)=>hs t.1 t.2.val (by omega) n
 unfold Atrium.shuffle;rw [Finset.sum_apply,Finset.sum_apply]; unfold Atrium.slip
 let g(o:O)(j:ℕ)(_hj:j ≤ e):= |tap j (N o i)| * c ((o,⟨e-j,by omega⟩))
 let a(o:O):=∑ j:Fin (e+1),g o j (Nat.le_of_lt_succ j.isLt)
 have ha(o):0 ≤ a o:=sum_nonneg fun j _=>mul_nonneg (abs_nonneg _) (hC _)
 refine ⟨∑ o,a o,sum_nonneg fun o _=>ha o,Sings.sum univ ?_ (fun o _=>ha o) ⟩
 intro o _;unfold a
 rw [← Fin.sum_univ_eq_sum_range]
 exact Sings.sum univ (fun u _=> (H (o,⟨e-u,by omega⟩)).smul _) (fun u _=>mul_nonneg (abs_nonneg _) (hC _))

def play {X:Labels.Frame G d}(Q:Crew G P K)(S:Bouquet X):Bouquet X:=fun i=>Q.land d (octave i) (S i)
def deposit (Q:Crew G P K)(S:Bh):M:= Atrium.ask (play Q S)
lemma overjoy (Q:Crew G P K)(S:Bh)(he:Threads D S):Threads D (play Q S)∧ Cloth (deposit X Q S):=by
 have H:Threads D (play Q S):=fun i=> Q.living D (S i) (he i) 
 exact ⟨H,cloth_request _ H⟩

-- one Live Deck through this stage Need.N.
theorem sleeved (h:Font d D k j t σ τ η μ V)(Q R:Crew G P K)(H:Race σ τ η μ V W δ D d k (d+k) j t Q R)(hδ:0<δ){S S':Bh}(hS:Threads D S)(hS':Threads D S')(he:Deck X D k h.fine S)(he':Deck X D k h.fine S'):Deck X D k h.coarse (play Q S)∧Deck X D k h.coarse (play R S'):=by
 let T:=play Q S;let T':=play R S';have hv:=overjoy X Q S hS;have hv':=overjoy X R S' hS'
 suffices H:∀ (i:O)(e:ℕ),e≤k→∀ n:ℕ,∃ B:ℝ,Dyad (stance _) D h.coarse B δ (T i e n) (T' i e n) from
    ⟨fun i e he n=>by obtain ⟨B,h⟩:=H i e he n;exact ⟨B,h.price,h.near⟩,fun i e he n=>by obtain ⟨B,h⟩:=H i e he n;exact ⟨B,h.price,h.far⟩⟩
 intro i e hx n; let l:=octave i
 by_cases hz:n≤l+e;swap
 · rw [show T i e n=0 from Classical.not_not.mp (fun h=>hz ((hv.1 i).inlet.lit _ _ h)),show T' i e n=0 from Classical.not_not.mp (fun h=>hz ((hv'.1 i).inlet.lit _ _ h))];exact ⟨0,Dyad.zero hδ.le⟩
 have hn:n≤d+k:= Nat.le_trans hz (Nat.add_le_add (octave_le i) hx)
 obtain ⟨Y,hy,F⟩:=portFee n e l
 let I:= Fin (e+1)
 choose C HC using fun n:I=> deckAll X he he' hS hS' hδ i n.val (by omega)
 let B:=∑ i:I,C i
 have hC(n:I):0≤C n:= (HC n 0 (by omega)).price
 have hB:0≤B:= sum_nonneg fun i _=>hC i
 have hJ(a r:ℕ)(hr:r≤l+a)(hh:a≤e):Dyad (stance _) D h.fine B δ (S i a r) (S' i a r):= (HC (⟨a,Nat.lt_succ_of_le hh⟩) r hr).mono (Finset.single_le_sum (f:=C) (fun i _=>hC i) (mem_univ _))
 have hk':= h.hired l e n (octave_le i) hx hz
 obtain ⟨ha,hf,h1,h2,-⟩:= F (H.aps.prices hx hn) hk'.out' hk'.warm (H.sold.nim.trans (half_le_self hk'.paid.le)) hB hB (hS i) (hS' i) (fun i r hr he=>hJ i r hr (by omega)) (hJ e n hz le_rfl)
 change ∃ (B:ℝ),Dyad (stance _) D h.coarse B δ (Q.land d l (S i) e n) (R.land d l (S' i) e n)
 rw [h1,h2];exact ⟨_,ha.add hf⟩
end YM.RG08.Sideshow
