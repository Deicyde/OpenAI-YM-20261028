import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Usual
import YM.Primitives.SMALL_FIELD_EXTERIOR.Squares
/-!
 # True exposed E6 Coat estimates. No choice-by-anchor to match accounts.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Deck
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f C F: Side} {P : Patch} {M : ℕ}
section drop
variable (h : C.val=c.val*M) (u : Directions G c)
local notation "p" => (Macrame.splitter (Deck.divides h))
local notation "w" => normal (Deck.divides h) h
include h
abbrev light {c C:Side} (f: Site C→ Site c) (u:Directions G c) : Directions G C :=u ∘ curr f
lemma lifted_base (V:Config G c): increment ((w).links V) (Deck.light p u)=(w).links (increment V u):=rfl
lemma hexed (i:Cell C): faceCurl i (toLog (Deck.light p u))=faceCurl (curr p i) (toLog u):= by
  rw [curl_eq,curl_eq]; dsimp only; simp only [Deck.light,curr,Function.comp_apply,Prod.map_apply, id_eq]; simp_rw [show ∀ i k,p (i+step k)=p i+step k from (w).step_up]; rfl
lemma stripped (P:Clip) (T:PathData G) (n : ℕ) (i:Twin C) : bareCut P T n (toLog (Deck.light p u)) i= bareCut P T n (toLog u) (dip p i) := by
  unfold bareCut; change (if i.2 then _ else _)=(if i.2 then _ else _); split
  · apply tsum_congr; intro j; change (if (T.row i.1.2 j).2.length≤ n then _ else _)=(if (T.row i.1.2 j).2.length≤ n then _ else 0); split
    · rw [hexed h]; let s:= T.row i.1.2 j
      have hp : curr p (slotFace s.2 i.1.1)=slotFace s.2 (p i.1.1) := Prod.ext ((w).rooted ..) rfl
      rw [hp]; rfl
    rfl
  exact congr_arg (fun v=> Real.sqrt P.direct • v) (hexed h u i.1)
end drop
section proj
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} (hC : C.val=c.val*M) (he:2 ≤ c.val)
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
include hC he
abbrev rod (u : Lace h H M) : Rod C F→ Rod c f:= Sum.map (dip u.high.cut) (curr u.low.cut) -- name collision L
lemma rod_nests : Nest (Deck.divides hC) (Deck.rod (L)) (focus (Y)) (focus (S)) := by
    have hx := (Deck.footing (h:=h) (H:=H) hC he).pr (E:=PlaqAxes) |>.pr (E:=Bool) |>.sum ((onfloor (h:=h) (H:=H) hC he).pr (E:=Axis)) -- dsimp
    convert hx using 2 <;> (ext1 i; cases i <;> rfl)
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {t : ℝ} {Pt:Teller G} (hT:P.Branches Q G)
include hT
lemma probing (u : Directions G f) (i:Bond C) : let v:= Deck.light (L).high.cut u
    zLin (Y) (toLog v) 0 i=zLin (S) (toLog u) 0 (curr (L).low.cut i):= by
  intro v; let V:= L; let k : (S).Choices:= Classical.arbitrary _; let z:=(L).pullTag Q k
  have ht := zTest_deriv (show (Y).patch.Branches (Y).kernel G from hT) z i (toLog v,0)
  have he j: zTest (Y) z i (j • (toLog v,0))=zTest (S) k (curr (L).low.cut i) ((j:ℝ) • (toLog u,0)):= by
    simp only [zTest, Prod.smul_fst, Prod.smul_snd, smul_zero]
    have hp (n:Side) (x: Directions G n) : j • toLog x= toLog (j • x):=rfl
    rw [hp,hp,edits, edits]; let W:= increment (1:Config G f) (j • u)
    rw [show increment (1: Config G F) (j • v) = (L).high.links W from lifted_base (fineP h H hC) (j • u) 1, Lace.predicts Q V]; rfl
  rw [funext he] at ht; exact ht.unique (zTest_deriv (show (S).patch.Branches (S).kernel G from hT) k (curr V.low.cut i) (toLog u,0)) -- arg
variable (ht:T'=re T)
include ht
lemma letdown (n:ℕ) (w : Directions G f) (i:Rod C F): barField T' n (Deck.light (L).high.cut w) i= barField T n w (Deck.rod (L) i):= by
  subst T'; rcases i with i|i; exact stripped (fineP h H hC) w T.high T.up n i; exact probing hC he hT w i
lemma sang (n:ℕ) (p:Rod C F) (hv : 2*(n+predReach P+4)<c.val) (w:Directions G f) (V:Config G c) : straightened T' n ((L).low.links V) (Deck.light (L).high.cut w) p= straightened T n V w (Deck.rod (L) p) := by
  let l:= L; let x:= focus (Y) p; let y:=focus (S) (Deck.rod l p); have hx : l.low.cut x=y:= (rod_nests (Q:=Q) (H:=H) hC he).footing p
  unfold straightened; rw [← letdown hC he hT ht]
  apply tangent_local T' (show (Y).patch.Branches (Y).kernel G from hT); intro i hi
  let z:= Shell.atEdge (Y) i; let k : Bond f:= curr l.high.cut i; have hz:l.low.cut z= Shell.atEdge (S) k:=(l.position i.1).symm
  suffices hg:carrier x (l.low.links V) z=carrier y V (Shell.atEdge (S) k) from congr_arg (fun p=>G.adjoint p (w k)) hg
  unfold carrier; rw [l.low.traveller,hx]; apply congr_arg _; unfold carriage; rw [← hx, ← hz]; exact congr_arg (fun x:Cover=>route 0 x 1) (starsL hC _ _ ((Nat.mul_le_mul_left 2 hi).trans_lt hv))
lemma wing (n:ℕ) (p:Rod C F) (hv : 2*(n+predReach P+4)<c.val) (w:Directions G f) (V:Config G c) (s:Signed) : orientedRow T' n s p ((L).low.links V) (Deck.light (L).high.cut w)= orientedRow T n s (Deck.rod (L) p) V w := by
  unfold orientedRow; rw [show pull s 0 ((L).low.links V)=_ from constellation hC s V,show replica (Y).ratio ((L).low.links V)=_ from Lace.Fitted.replicate (L) V]
  rw [show displacement s (Deck.light (L).high.cut w) ((L).high.links (replica (L).r V))= Deck.light (L).high.cut (displacement s w (replica (S).ratio V)) from orbitData (fineP h H hC) s (replica (S).ratio V) w]; exact sang hC he hT ht n p hv ..
end proj
end YM.PhysicalNext.Repeat.Deck
