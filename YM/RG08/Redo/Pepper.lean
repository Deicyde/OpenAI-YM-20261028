import YM.RG08.June.Hold
import YM.RG08.Aura.Cast
import YM.RG08.Redo.Pit
/-! # Demand strengthening. Before L pre assets, after L logBeta parks. knots
 announced uniformly *before stages*, adjacent J,J+1 closure, no μ paid by post!
-/
noncomputable section
namespace YM.RG08.Redo
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Rate.Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Camera Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason
open PhysicalNext PhysicalNext.Repeat Next.Free Function Jetty Skiff Weald Hatch Planned.PrimaryIntegral295 Labels Source Source.Drops WardBin Parts Atrium Trill Necks Sideshow April Yurt Filter
open scoped Classical Matrix BigOperators PowerSeries Topology ENNReal
set_option autoImplicit false
variable {O X:Type}(G:Gauge)(K:KernelChoices)(P B:MapPrices){d D e k j t:ℕ}
local notation "T0"=> RG08.Supplies.stone
local notation "E₀"=> Loc G 1
-- total outside t≥4 region (1)
structure Beverage where
 τ: ℝ
 pos : 0<τ
 V: ℝ
 alive:0≤V
 C:Patch→ℝ
 held i: 0 ≤ C i
def snack(j t:ℕ):Beverage:=if h:4≤j∧4≤t then
 let T:= Aura.guide G K P j t h.1 h.2
 ⟨T.choose,T.choose_spec.1,T.choose_spec.2.choose,T.choose_spec.2.choose_spec.1.le,fun p=> T.choose_spec.2.choose_spec.2.choose p.L.val p,fun i=>T.choose_spec.2.choose_spec.2.choose_spec.1 i.L.val i⟩
 else ⟨1,by norm_num,0,le_rfl,fun _=>0,fun _=>le_rfl⟩
-- output port widths depend only pre stage j (coarse) and allow next step t=j or j+1. no fine/output restriction otherwise.
def reef (E i:ℕ):ℝ:=min (min ((snack G K P i i).τ/2) ((snack G K P (i+1) i).τ/2)) (min 1 (Yamen.honesty G P B K i E))
lemma reef_life(E i:ℕ):0<reef G K P B E i:= lt_min (lt_min (half_pos (Beverage.pos _)) (half_pos (Beverage.pos _))) (lt_min zero_lt_one (Yamen.honesty_pos ..))
lemma reef_cap(E i:ℕ):reef G K P B E i≤ min 1 (Yamen.honesty G P B K i E):=min_le_right ..
lemma reef_crown(E i j:ℕ)(ht:j=i∨j=i+1):2*reef G K P B E i≤ (snack G K P j i).τ:=by
 rcases ht with rfl|rfl
 · have he:reef G K P B E j ≤ (snack G K P j j).τ/2:=le_trans (min_le_left ..) (min_le_left ..);linarith only [he]
 have he:reef G K P B E i ≤ (snack G K P (i+1) i).τ/2:=le_trans (min_le_left ..) (min_le_right ..);linarith only [he]
-- demand list joint representation. Through ALL e ≤ k, d horizon, D derivative beam;
-- admits if d+2≤fine & D ≤ J at coarsest. E = 2*(D+k+1), padded unmarked.
structure Cup where
 d:ℕ
 D:ℕ
 k:ℕ
 paid:d+1≤D
namespace Cup
abbrev E(R:Cup):ℕ:=2*(R.D+R.k+1)
lemma admits(R:Cup):Live 0 R.E∧R.k<R.E∧R.d+2≤R.E∧R.D≤R.E:=by
 constructor
 · constructor;omega
   rw [Nat.zero_add];exact even_two_mul _
 have h:=R.paid; unfold Cup.E; omega
end Cup
structure Note (R:Cup)(j t:ℕ):Prop where
 neighbor:j=t∨j=t+1
 base:4≤t
 demand:R.E≤t
lemma Note.titles {R:Cup}{j t:ℕ}(h:Note R j t):4≤j∧4≤t∧R.d+2≤j:=by have he:=h.base;have hz:=h.neighbor;have ht:=h.demand;have h:=R.admits;omega
local notation "M"=>reef G K P B
local notation "N"=>snack G K P
structure Suit (F:Labels.Frame G d)(D k E j t:ℕ) where
 μ:ℝ
 seat:Font d D k j t (M E j) (N j t).τ (M E t) μ (N j t).V
 threshold:ℕ
 insure (L:Side): threshold ≤ L.val→(2*M E t)/(L.val:ℝ)≤μ∧ M E t * Carrier.unitStep L ≤ M E j/2∧∀ (e l n:ℕ)(he:e≤k)(hl:l≤d)(hn:n≤l+e),(April.cap F D k j t l e n (Next.Foundations.hol G) K (M E j) (M E t) (N j t).τ μ (N j t).V seat hl he hn)^2 ≤ (L.val:ℝ)
def cover (R:Cup)(j t:ℕ)(h:Note R j t):Suit G K P B ((Labels.frames G).level R.d) R.D R.k R.E j t:=
 let V:=June.rungs ((Labels.frames G).level R.d) R.D R.k j t (Next.Foundations.hol G) K (M R.E j) (N j t).τ (M R.E t) (N j t).V (reef_life ..) (reef_life ..) ((reef_cap ..).trans (min_le_left ..)) (reef_crown _ _ _ _ _ _ _ h.neighbor) (Beverage.alive _) R.paid h.titles.1 h.titles.2.1 (by have hh:=h.titles;omega)
 ⟨V.choose,V.choose_spec.choose,V.choose_spec.choose_spec.choose,V.choose_spec.choose_spec.choose_spec⟩
-- our row streams in hmeet. Use λ chosen
lemma concession {a:Levels G}{H:Horizon a}(hK:a.clock.kernel=K)(hF:H.Suffices P)(hE:Aura.licensed a H){N0 m:ℕ}(hi:m<N0)(hj:a.clock.J (m+1)=j)(ht:a.clock.J m=t){R:Cup}(hq:Note R j t):
 let s:=N j t;let u:=T0 a m; let b:=Cell.plotted u K G (H.H N0 (m+1))
 ;∀ A≥ s.C u,RowCost s.τ u.L b A∧
 ∃ (F: Next.Free.Flight j t)(x:u.L=F.L)(Y:Kernel G.ColorIndex (Loc G 1)),RowCost s.τ u.L Y A∧
   (Yurt.Tutor u.L s.τ s.V (x.symm ▸ Carrier.linesOf F K.penalty) G R.d) ∧ Yurt.Crest u.L (x.symm ▸ Carrier.linesOf F K.penalty) Y b:=by
 intro s u b A hv
 have hσ:4≤j∧4≤t:=⟨hq.titles.1,hq.titles.2.1⟩
 obtain ⟨hV,hA,hS,hB⟩:= (Aura.guide G K P j t hσ.1 hσ.2).choose_spec.2.choose_spec.2.choose_spec.2 a H N0 m hF hE hi hK hj ht
 have hch {I J}{F:Kernel I J}(h:RowCost s.τ u.L F (s.C u)):RowCost s.τ u.L F A:= fun i j=> (h i j).trans (ENNReal.ofReal_le_ofReal hv)
 constructor
 · apply hch
   unfold s snack; rw [dif_pos hσ];rw [Aura.rootK,hK] at hA; exact hA
 -- Frames dependent choices. cases equalities then X explicit by rfl
 let Y:=Aura.sprout G a H N0 m
 subst K;subst j;subst t
 refine ⟨destination a N0 m,rfl,Y,hch ?_, ?_,fun y z=>?_⟩
 · unfold s snack;rw [dif_pos hσ];exact hS
 · intro w hw; unfold s snack; rw [dif_pos hσ]; rw [Nat.add_comm w.length 1]; exact hV _ (by have hs:=hq.titles; omega)
 obtain ⟨k,⟨i,c⟩⟩:=z
 obtain ⟨x,rfl⟩:=axisEquiv.surjective i
 rw [coord_map]
 simp only [Flint.grad,Quarry.back_axis]; change Aura.rootK G a H N0 m _ _= Aura.oracle _ _ _ _ _ _+_; exact hB y k x c
end YM.RG08.Redo
