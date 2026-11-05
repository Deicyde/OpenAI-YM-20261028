import YM.MergeProof.North.Dolphin
import YM.MergeProof.North.Flank
import YM.MergeProof.North.Harvest
import YM.MergeProof.North.Ossola
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
import YM.MultipleContact.Bunch.Calm
import YM.MultipleContact.Bunch.Ebb
import YM.MultipleContact.Bunch.River
import YM.MultipleContact.Bunch.Liturgy
import YM.MultipleContact.Bunch.Papyrus
import YM.MultipleContact.Bunch.Wings
import YM.MultipleContact.Bunch.Palate
import YM.MultipleContact.Bunch.Anise
import YM.MultipleContact.Bunch.Platform
import YM.MultipleContact.Bunch.Islands
import YM.MultipleContact.Bunch.Quiet
import YM.MultipleContact.Bunch.Price
import YM.MultipleContact.Bunch.Antique
import YM.MultipleContact.Bunch.Apiary
import YM.MultipleContact.Bunch.Stable
import YM.MultipleContact.Bunch.Belvedere
import YM.MultipleContact.Bunch.Thunder
import YM.MultipleContact.Bunch.Dolphin
import YM.MultipleContact.Bunch.Aeolus
import YM.MultipleContact.Bunch.Lichen
import YM.MultipleContact.Bunch.Flank
import YM.MultipleContact.Bunch.Harvest
import YM.MultipleContact.Bunch.Muscat
import YM.MultipleContact.Bunch.Fram
import YM.MultipleContact.Bunch.Ossola

/- generalized from YM.MergeProof.North.Arco to arbitrary arity -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.MergeProof.BatchRibbons
variable {slot:Type}[Fintype slot][DecidableEq slot][Inhabited slot]
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent BatchRibbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
section
variable {V : Type}[Fintype V][DecidableEq V]{G:Gauge}(C:Family G) (N m p d:ℕ){W:Bid.Worth}{u ψ φ δ: ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}
    {D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "H"=> C.path
local notation "P'"=> C.path.levels.budget
local notation "R"=> C.path.rep N p
local notation "Q'"=> C.path.levels.budget (m+1)
local notation "M"=> (Labels.frames G).level d
local notation "U"=> Next.Foundations.localSection G d
variable (E:∀ i:ℕ,V→Site (C.side i p))(o:∀ i:ℕ,Name V slot→Site (C.side i p))(P:V→ Motion)(v:V)(B:V→Equiv.Perm V)
    (J:V→ℝ)(t:slot→ℕ) (s: (i:slot)→ C.label (t i)) (q:slot→Motion)(a:slot→ℝ) (F:Name V slot→ Config G (C.side N p)→ℂ)
    {σ χ:ℕ→ℝ}{μ j:ℕ}{l:ℕ}{η A x:ℝ} (hN:j<N)(hm:m+1<j) (h:C.Makes)(hh:Geyser C W u ψ φ δ ζ r D)(hr:Thor (slot:=slot) C.path δ r D σ χ μ)(ht':μ ≤ m)
local notation "Ω"=> (fun i=>MergeProof.item C (t i) N p (s i) (fun j=>o j (v,i)) (q i)) -- edit
local notation "W₀"=> (fun b:slot=>δ j*(φ j*a b))
local notation "y"=> (fun b:slot=>δ (m+1)*krill C.path.S j (m+1+1) (W₀ b))
local notation "g₀"=> Salt.tow (fun i:Name Unit slot=>y i.2) ((P' (m+1)).supportExponent+1/2) η l
local notation "k₀"=> Salt.scent (slot:=slot) (P' (m+1)).B (r (m+1)) ((P' (m+1)).supportExponent+1/2) 1 η 1 (χ (m+1))
local notation "h!"=> lt_of_lt_of_le (Nat.lt_succ_self m) (le_trans hm.le hN.le)
include h hh hr ht'
set_option maxHeartbeats 500000 in
lemma sail (hk:C.ref d ≤ m+1)(ht:∀ i,C.ref (t i) ≤ j)(hM:∀ i,a i*Spindle.paid C (t i) j N p (s i) ≤ ζ (t i) j)(hw:∀ i,0<a i)
   (hA: Migrating H m p N E) (hB:P v=(1,false))(hc:E m v=0)(he:∀ i,o (m+1) (i,(default:slot))=E (m+1) i)(hP:∀ i,i≠v→B i v=i)(hO:∀ b:ℕ,m+1 ≤ b→b≤N→∀ i,i≠v→∀ j:slot,o b (i,j)=affine (P i).1 (E b i) (o b (v,j)))
   (hK:Migrating H j p N o)(hF:∀ i:ℕ,m+1 ≤ i→i<j→(C.path.levels.clock.op i p).ratio.parent ∘ o (i+1)=o i)(hi:∀ i,m+1 ≤ i→i ≤ j→ Occupancy (o i) (r i))(hS:∀ i,m+1 ≤ i→i ≤ j→ Drake (Aged V slot) (P' i).B (o i)) (hV:∀ i,i≠v→∀ b:slot,F (i,b)=stepUp (P i) (E N i) (F (v,b)))(hy:∀ i,F (v,i)=Ω i)(hX:Integrable (birth (Aged V slot) (R N) F) (prior G _))
   (hx':χ j≤1)(hY:∀ i:ℕ,m+1 ≤ i→∀ hi:i<j, MergeProof.Float.Runs (D N p i (hi.trans hN)) (C.path.levels.clock.op i p) (6*((C.S.block i).val:ℝ)))
   (hI:Occupancy (E m) (r m))(hI':Occupancy (E (m+1)) (r m))(hη:0<η)(hq:η≤1)(hy':∀ i:V, coverNumber (Q').B (univ.image fun s:slot=>o (m+1) (i,s)) ≤ l)(hFq: (( (Q').B + (Q').B+1 :ℕ):ℝ)^4*k₀ ≤ 1/2)(hΔ:Real.exp k₀-1≤1)
   (hx0:A=(∏ b:slot,g₀ ((),b))) (hJ:∀ i,0<J i)(hZ:∀ i,J i ≤ δ m * (A/(16*x)))
   (hD: Throws C.path N p m (D N p m h!) (Next.Foundations.hol G) U x)(hx:1 ≤ x) :
   let Z:=C.S.a (m+1)^d*(x*(4*(1/A)))
   ∃ Q₀: Coefficient M (C.side m p), Q₀.Format 0 (Next.Foundations.hol G) (R m) ∧ Q₀.remBound 0 (R m) (kappa C.path m) Z ∧ (M).coeffSize Q₀.x ≤ Z ∧
       Served (R m) (fun i=> radiant (alto H m d) (P i) (E m i) (Q₀.exponentialEntry 0 U (R m))) (fun i=> sunny (R m) Q₀.forced (P i) (E m i) (alto H m d)) (gust C.path N p N (birth (Bud V) (R N) (fun i c=> ∏ b:slot, F (i,b) c)) m (h!).le) (E m) J ((P' m).supportExponent) 1 :=by
   let Y:= gust H N p N (birth (Aged V slot) (R N) F); let U':= birth (Bud V) (R N) (fun i c=> ∏ b:slot, F (i,b) c); let Y':=gust H N p N U'; have hΔ':= ht'.trans m.le_succ
   obtain ⟨L₀,g,K,hg,hb,hU⟩:= upper C t N j p W u ψ φ δ ζ r D s o q a v E P B F σ χ hh h hr (hΔ'.trans hm.le) ht hN (hi _ hm.le le_rfl) hK (hS _ hm.le le_rfl) hM hw ⟨fun i he=>hA.mare i (by omega)⟩ hP (fun i he=>hO i (by omega)) hV hy hX
   obtain ⟨-,hf,-⟩:= (hh.heights d (m+1) N p hk (hm.trans hN|>.le)).choose_spec
   have hF':Brine C.path (m+1) δ φ:=⟨fun i _=> hh.stay.water _ (Nat.zero_le i),fun i _=> hh.stay.mint _ (Nat.zero_le i),fun i _=> hh.stay.split _ (Nat.zero_le i),fun i _=> hh.stay.support _ (Nat.zero_le i)⟩
   have ht(i): 0 < W₀ i:= mul_pos (hr.suns j (hΔ'.trans hm.le)|>.hats.1) (mul_pos (hF'.water j hm.le|>.1) (hw _))
   have hL(i:ℕ)(hi:0 ≤ i):2 ≤ ((C.S.block i).val:ℝ):=by exact_mod_cast (le_trans (by norm_num) (C.S.block_large i) : 2 ≤ (C.S.block i).val)
   have hd:Arsenal (R j):=by
      let c:=D N p (j-1) (by omega); cases j with
      | zero=> omega
      | succ j=> exact (hr.moon N p j (by omega) (by omega)).1.contact
   obtain ⟨g',K',hZ',hφ⟩:= ossuary H δ r D E o P v (W₀) B σ χ h.wilson hr hΔ' ⟨fun i he=>hA.mare i (by omega)⟩ (fun i _ hp=> gust_step C.path _ p _ _ hp) (fun i _ hi=> gust_live C.path N p _ _ hX hi) (fun i he hx=> hO _ he (hx.trans hN.le)) hN.le hY hm g K _ hU hb ht hg hx' hd (fun i _ _=>hL i (Nat.zero_le _)) φ hF' (fun i h _=>hf.level i h) hS hh.mom (hi _ le_rfl hm.le) hF
   have hW:=hA.mare m le_rfl h!
   let I:= (fun _:V=> A/(16*x)); let w :Name V slot→ℝ:= fun i=> y i.2; have hv(i):0 < w i:= mul_pos (hr.suns _ hΔ'|>.hats.1) (mul_pos (div_pos (ht i.2) (by norm_num)) (pow_pos (div_pos (C.S.a_pos _) (C.S.a_pos _)) _))
   let g':= Salt.tow w ((Q').supportExponent+1/2) η l -- shadows
   have hA'(i:V): A=(∏ b:slot,g' (i,b)):=hx0; have hδ:0 < δ m:=(hr.suns m ht').hats.1; have hw(i):0 < g' i:= Salt.towP w _ η l hv hη _; have hx':0 < x:= zero_lt_one.trans_le hx; have hp:0 < A:=by rw [hA' v]; exact prod_pos fun _ _=>hw _
   let z:= C.path.levels.clock.op m p; have hH:(fun i=> (C.path.levels.clock.op m p).ratio.embed (E m i))= E (m+1):= hW
   intro Z; rw [gust_step C.path N p N _ h!]; have ht':= hx0
   have hb'(i):0 < I i:= div_pos hp (by positivity)
   have hu : A/x≤ A:= div_le_self hp.le hx
   have hε : Repegs (E m) (P' m).B (fun i=>δ m*I i) J (1/2) 1 (Bud V):=by
       intro i he j hj; rw [one_mul]; exact (prod_le_prod (fun i _=>hJ i|>.le) (fun i _=>hZ i)).trans (le_mul_of_one_le_right (prod_nonneg (fun i _=>mul_nonneg hδ.le (hb' i|>.le))) (Real.one_le_exp (by positivity)))
   have hZ0 := dusks H N m p d δ r D (E m) (o (m+1)) P v B I J w σ χ l η A x h! (Y _ h!) (Y' _ h!) h.wilson hr ‹μ ≤ m› hc (fun i=>(he i).trans (congr_fun hH.symm i)) hB hI (hH.symm ▸ hI') (fun i hu=>⟨hP i hu,fun j=>⟨by rw [hH]; exact hO _ le_rfl h! i hu j,hb i hu j⟩⟩) hv hφ _ K' _ (hH.symm ▸ hZ') (glean H _ _ F hX _) (gust_live H N p N _ (glean_in H _ _ F hX) h!) hη hq (hi _ le_rfl hm.le) hy' hFq hΔ hb' hJ ?_ (hA' _) ?_ ?_ hε hD hx'.le; exact hZ0
   · intro i; exact (div_le_self hp.le (show (1:ℝ) ≤ 16*x from by linarith only [hx])).trans_eq (hA' _)
   · intro i; unfold I; field_simp; linarith only [hx,hp]
   intro i; set L' := ((C.path.S.block m).val:ℂ)^d
   have hL':1 ≤ ‖L'‖:= by unfold L'; rw [norm_pow,Complex.norm_natCast]; exact one_le_pow₀ (le_trans one_le_two (hL _ (Nat.zero_le _)))
   have hν: ‖L'⁻¹‖ ≤ 1:= by rw [norm_inv]; exact inv_le_one_of_one_le₀ hL'
   refine (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (mul_nonneg hx'.le (by positivity)) hν) (hb' i).le).trans ?_; unfold I; field_simp; linarith
end
end YM.MergeProof.BatchRibbons
