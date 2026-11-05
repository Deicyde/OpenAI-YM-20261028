import YM.MergeProof.Badlands
import YM.MergeProof.North.Anise
import YM.MergeProof.North.Elders
import YM.MergeProof.North.Lamplit
import YM.MergeProof.North.Thunder
import YM.Next.RANK.ScaleScale
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

/- generalized from YM.MergeProof.North.Dolphin to arbitrary arity -/

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
variable {V : Type}[Fintype V][DecidableEq V]{G:Gauge}(H:History G) (N m p d:ℕ)(δ:ℕ→ℝ)(r:ℕ→ℕ)
    (D:∀ N p m:ℕ,m<N→GaugeDoor (H.rep N p (m+1)) (H.rep N p m))
set_option quotPrecheck false
local notation "R"=> H.rep N p
local notation "P'"=> H.levels.budget
local notation "Z"=> H.levels.clock.op m p
local notation "Q"=> H.rep N p (m+1)
local notation "Q'"=> H.levels.budget (m+1)
local notation "L'"=> (↑(H.S.block m).val:ℂ)^d
local notation "F"=> (Labels.frames G).level d
local notation "U"=> Next.Foundations.localSection G d
variable (E:V→Site (H.S.side m p))(o:Name V slot→Site (H.S.side (m+1) p))(P:V→ Motion)(v:V)(B:V→Equiv.Perm V)
    (I J:V→ℝ)(w:Name V slot→ℝ)
    {l:Name V slot→ℂ}(σ χ:ℕ→ℝ){μ:ℕ}(t:ℕ)(η A x:ℝ)
    (hN:m<N)(Y:Config G (H.S.side (m+1) p)→Poly (Aged V slot)) (Y':Config G (H.S.side (m+1) p)→Poly (Bud V))
    (h:H.Selected) (hr:Thor (slot:=slot) H δ r D σ χ μ)(ht':μ ≤ m)
local notation "s!"=> Salt.scent (slot:=slot) (P' (m+1)).B (r (m+1)) ((P' (m+1)).supportExponent+1/2) 1 η 1 (χ (m+1))
local notation "W!"=> Salt.tow w ((P' (m+1)).supportExponent+1/2) η t
local notation "Ω"=> (fun i : V=> (Z).ratio.embed (E i))
local notation "U'"=> (fun i : V=>(∏ b:slot, W! (i,b)))
omit [Fintype V] in
lemma stepid {n:Side}(x:Config G n→ℂ) : stepUp (1,false) (0:Site n) x=x:=Motion.dance_nil x
lemma floatid {n:Side}(x:Res G n): floatUp (1,false) (0:Site n) x=x:=by
    have ht (i:Support n): sky (1,false) (0:Site n) i=i:=by rw [shading]; change i.image (affine (1:Signed) (0:Site n))=i; rw [show affine (1:Signed) (0:Site n)=id from funext fun x=>by simp [affine]]; simp
    let t:= puff (1,false) (0:Site n); funext p; obtain ⟨p,rfl⟩:= t.surjective p; unfold floatUp; rw [stepid]; change x (t.symm (t p))= _; rw [Equiv.symm_apply_apply]; exact congr_arg x (Prod.ext (ht _).symm (ht _).symm)
include hN h hr ht'
local notation "a"=> 4*((1:ℝ)/A)
lemma dusks (hE: E v=0)(ho:∀ i,o (i,(default:slot))= (Z).ratio.embed (E i))(hW:P v=(1,false)) (hO:Occupancy E (r m))(hO':Occupancy Ω (r m)) (he:∀ i,i≠v → B i v=i ∧ ∀ j:slot,o (i,j)=affine (P i).1 (Ω i) (o (v,j))∧l (i,j)=scalar (P i) (l (v,j))) (hw:∀ i,0<w i)(hT:∀ i,w i * ‖l i‖≤1)
   (F' L t') (hU:Arc Q F' L Y v P (Ω) B o w ((Q').supportExponent+1/2) ((Q').supportExponent+1) 1 (χ (m+1)) t' l) (hp:Y'=fun c=>reap (Y c))(hh:Integrable Y' (prior G _))
   (hη:0<η)(hq:η≤1)(hf:Occupancy o (r (m+1)))(hy:∀ i:V, coverNumber (Q').B (univ.image fun s:slot=>o (i,s))≤t)(hF: (( (Q').B + (Q').B+1 :ℕ):ℝ)^4*s! ≤ 1/2)(hΔ:Real.exp s!-1≤1)
   (hI:∀ i,0<I i)(hJ:∀ i,0<J i)(hX:∀ i,I i≤ U' i)(hA:A= U' v) (hc:∀ i,2*I i*(2*a)≤1)(hz:∀ i,I i*(‖(L')⁻¹‖*(x*a))≤1) (hε:Repegs E (P' m).B (fun i=>δ m*I i) J (1/2) 1 (Bud V))
   (hD: Throws H N p m (D N p m hN) (Next.Foundations.hol G) (U) x)(hx:0≤x) :
   ∃ Q₀: Coefficient F (H.S.side m p), Q₀.Format 0 (Next.Foundations.hol G) (R m) ∧ Q₀.remBound 0 (R m) (kappa H m) (H.S.a (m+1)^d*(x*a)) ∧ (F).coeffSize Q₀.x ≤ H.S.a (m+1)^d*(x*a) ∧
       Served (R m) (fun i=> radiant (alto H m d) (P i) (E i) (Q₀.exponentialEntry 0 U (R m))) (fun i=> sunny (R m) Q₀.forced (P i) (E i) (alto H m d)) ((Z).push ((Q).beta) Y') E J ((P' m).supportExponent) 1 :=by
   have h':= h.represents N p (m+1) hN; have hu:= h'.vac; have hV:= (hr.moon N p m ht' hN).1
   obtain ⟨g,L₀,hL,hK,hP⟩:= grafted (r (m+1)) t η 1 1 hV.contact (hu.symm ▸ hU) h'.good.labels he hw hf zero_le_one hT ((Q).p.B_pos) hη hq (fun i=>by rw [hu]; exact hy i) (by norm_num) (by norm_num : (1:ℝ)/2≤1) (fun b=>(Tour.bright H h N p _ hN b).ne') (w:=U') (by intro i; rw [hu]) (hu.symm ▸ hF) (hu.symm ▸ hΔ)
   have hc': (fun i:V=>o (i,(default:slot)))= Ω:=funext ho
   rw [← hp,hu,hc'] at hL
   let f':= fun i=>profile (Q).activities (L₀ i); have hw'(i):0 < U' i:=lt_of_lt_of_le (hI i) (hX i); have hC := hL.prune hw' hI (slighter hw' hI (w:=1) (fun i=> (hX i).trans_eq (one_mul _|>.symm)) zero_le_one le_rfl) zero_le_one (show (Q').supportExponent+0≤ (Q').supportExponent from by simp) (show 1*1≤ (1:ℝ) from by norm_num)
   have hβ:(Ω v)=0:=by dsimp only; rw [hE]; exact (Z).ratio.root.map_zero
   have ha : Blade Q 0 (g v) (f' v) 0 (a):=by rw [hA]; exact (congr_arg (fun i=>Blade Q i _ _ _ _) ((ho v).trans hβ)).mp (hK v|>.2)
   have hb(i):g i = stepUp (P i) ((Z).ratio.embed (E i)) (g v)∧ f' i=floatUp (P i) ((Z).ratio.embed (E i)) (f' v):=by
       by_cases hi:i=v
       · subst i; rw [show (Z).ratio.embed (E v)=0 from hβ,hW,stepid,floatid]; exact ⟨rfl,rfl⟩
       exact hP i hi
   obtain ⟨Q₀,hY,hσ,hB,hX⟩:= MergeProof.Ribbons.fuseNext H d r h hN (hr.suns m ht') hV hI hJ hC (by linarith only) hO' (by rw [show (Z).ratio.parent ∘ Ω=E from funext (fun i=> (Z).ratio.embed_parent _)]; exact hO) (fun i=> (hK i).1) ha rfl hb hD hx hc hz hε hh
   refine MergeProof.Ribbons.crescent H d hY hσ hB hX
end
end YM.MergeProof.BatchRibbons
