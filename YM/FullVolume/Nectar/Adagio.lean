import YM.FullVolume.Nectar.Nail
import YM.FullVolume.Florid.Flock
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Ray
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond PhysicalNext.Repeat Greenbelt Lotus Merge Merge.Palette Merge.Switch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {A:Type} [Fintype A] {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Ovens
variable (H:Cash W x μ L Q o C T R)
structure Tier (t:A→Wing)(g:A→ℕ)(f:sun→A→Leaf R):Prop where
   modeS (y:sun)(i):(f y i).turn=t i
   habit (i:A) (U:Config G _):Nail (g i) (fun y=> (f y i).ingredient U)
namespace Tier
variable {w:A→Wing} {b:A→ℕ} {p:sun→A→Leaf R} (h:Tier w b p) (X:Coat T F)
set_option quotPrecheck false
include h
local notation "X₀" => fun i:A=> (w i).badge S
variable (i:Tickets fun a:A=>(w a).badge S) (U:Config G c)
-- transport for exact votes
lemma signs (x:sun) : sign (p x) S=X₀:= funext fun i=>congr_arg (fun z:Wing=>z.badge S) (h.modeS x i) -- S implicit

def jump (x:sun): Tickets (fun a=> (w a).badge S)≃ Tickets (sign (p x) S):= Equiv.setCongr (t:=setOf (Draft (sign (p x) S))) (s:=setOf (Draft ((X₀)))) (by rw [h.signs]) -- edit
local notation "Hp" y:max => team (p y) (h.jump y i)
lemma ticket (y:sun):(h.jump y i).val=i.val:= rfl
lemma land (y:sun) : (Hp y).signs S=i.reach:=by
    rw [label]; unfold Tickets.reach; rw [ticket,h.signs]
omit [Fintype A] in
private lemma descendK (y:sun) : Set.InjOn (p y) (i.val:Set A):=by
    intro a ha j hj het; apply i.property ha hj; exact congr_arg (fun e=>e.badge S) (show w a=w j from (h.modeS y a).symm.trans ((congr_arg Leaf.turn het).trans (h.modeS y j)))
set_option quotPrecheck false
local notation "η"=> (∑ j∈i.val, b j)
lemma coal (l:ℝ) (a : Directions G f): Nail (∑ j∈i.val,b j) (fun y : sun=> (Hp y).paidU X l a):=by
   have he(j): Nail (b j) (fun y=> (p y j).paidU X l a):= by
      unfold Leaf.paidU Leaf.fond; simp_rw [h.modeS];exact (h.habit j _).mul_right _
   have hp:=Nail.all i.val (fun j (y:sun)=> (p y j).paidU X l a) b (fun i _=> he i)
   unfold Team.paidU team;dsimp only; simp_rw [ticket, Finset.prod_image (h.descendK i _)]; exact hp
lemma leagues (s:Molecule S) (k:Finset ℕ)(z:F.Slice G×Air f G): Nail (∑ j∈i.val,b j) (fun y:sun=> (Hp y).into X W a Ñ k m s z):=by
   unfold Team.into Team.premium; simp_rw [h.land]; split_ifs; exact (h.coal _ i _ _).mul_right _; exact Nail.const _
lemma skim (s:Molecule S)(k:Finset ℕ) (Y:Cash W X.x μ L Q o C T R) (he:X.manifest)(hh:X.width=o.K): Nail (∑ j∈i.val,b j) (fun y:sun=> (Hp y).tithe X k W o.a Q.table Q.halo s):= by
   apply Nail.integral; exact h.leagues X i s k
   exact fun y=>(Team.tip _ X _ Y hh he s).2.1
lemma breeze (s:Molecule S)(Y:Cash W X.x μ L Q o C T R)(hh:X.width=o.K): Nail (∑ j∈i.val,b j) (fun y:sun=> (Hp y).bloom X W o.a Q.table Q.halo s):=by
   unfold Team.bloom; split_ifs; · unfold Team.steep likely; exact Nail.mul_left (Nail.net Finset.univ _ fun l _=>h.skim ((planted X s).taggedL l) i s _ Y (planted_valid X s) hh) _
   exact Nail.const _
lemma votes (χ:Chi)(x:Molecule S):Nail (∑ j∈i.val,b j) (fun y:sun=> Palette.act (p y) H χ U x ((h.jump y) i)):= Nail.mul_left (Nail.net _ _ fun k _=> h.breeze (Greenbelt.prism T _ χ _ U (allot k)) i x H rfl) _
variable (Cy:A→ℝ)(χ:Chi)
lemma party (s:Molecule S): Bed b (fun t:sun=> Palette.vote (p t) H χ Cy s U):=by
   let f (i:Tickets (X₀)) t:= Switch.click i.val ((∏ j∈i.val,Cy j)*Palette.act (p t) H χ U s (h.jump t i)); have he t(l:ℝ)(i:Finset A):Palette.vote (p t) H χ Cy s U l i=∑ j,f j t l i:=by
      unfold Palette.vote color; rw [←Equiv.sum_comp (h.jump t)]; apply sum_congr rfl; intro j _; rw [amplitudes]; unfold f;rw [ticket]; unfold click; split_ifs <;> ring
   rw [show (fun t:sun=> Palette.vote (p t) H χ Cy s U)=∑ j,f j from funext fun t=> funext fun l=> funext fun i=> by rw [he]; simp]; exact Bed.many f _ fun i _=> Bed.clickY _ ((Tier.votes H h i U χ s).mul_left _)
open Gas Ursell Trees Multiple Letter OmitClusters
lemma markSong (s:H.fragrances) : Bed b (fun t:sun=>Palette.song (p t) H χ Cy s U):=by
    let z:= (s.1+1).factorial; let a:=coefficient H.seam s.2/(z:ℝ); let f k (t:sun):= Palette.vote (p t) H χ Cy (s.snd k).val U
    have he: (fun t:sun=> Palette.song (p t) H χ Cy s U)=a • (∏ i,f i):=by
       funext t x y; simp only [Pi.smul_apply,Finset.prod_apply, smul_eq_mul]; unfold Palette.song Cash.trainedMill Gas.term; change coefficient H.seam s.snd*(∏ i,f i t x y)/(z:ℝ)= _; unfold a; ring
    rw [he]; exact Bed.spray (Bed.seals f _ (fun i _=>Tier.party H h U Cy χ _)) _
lemma markTones (s:H.fragrances) : Bed b (fun t:sun=>Photo.tones (p t) H χ Cy s U):=by
    let f(t:sun):=Palette.song (p t) H χ Cy s U; have hp(t:sun): Palette.ways Cy 0 ∅=fun _=>0:=by funext i; simp [Palette.ways]
    let a:=H.trainedMill (H.spawn χ U) s
    rw [show (fun t:sun=> Photo.tones (p t) H χ Cy s U)=f+(fun _ _ _=>-a) from (funext fun t=> funext fun i=>funext fun l=>by unfold Photo.tones;change f t i l-Palette.song (p t) _ _ _ _ _ _ _=f t i l+-a;unfold Palette.song; rw [hp t,muted]; exact sub_eq_add_neg ..)]
    exact (h.markSong H U Cy χ s).plus (Bed.casket _)
lemma markColony (j:H.Chapter) : Bed b (fun y:sun=>fun l s=>H.cologneMill (fun i=>Palette.vote (p y) H χ Cy i U l s) j):=by
    rcases j with i|i; exact Tier.party H h U Cy χ _
    let f(t:sun):=Palette.song (p t) H χ Cy i U; have hv: Bed b ((-1:ℝ) • f):= Bed.spray (Tier.markSong H h U Cy χ i) _
    convert hv using 1; ext; simp; rfl
lemma markFete (j:H.Chainbook) : Bed b (fun t:sun=> Palette.fete (p t) H χ Cy j U):= by
    unfold Palette.fete Cash.smilesMill; split_ifs
    · let n(i:↥j.1):= j.2 i+1; let e(i:↥j.1):ℝ:=((n i).factorial:ℝ)⁻¹; let f(i:↥j.1)(t:sun)(l:ℝ)(s:Finset A):= H.cologneMill (fun j=>Palette.vote (p t) H χ Cy j U l s) i.val; let g i:=e i • ((f i)^(n i));
      have hp(i): Bed b (g i):= ((Tier.markColony H h U Cy χ _|>.pour (n i)).spray _)
      convert Bed.seals g Finset.univ (fun i _=>hp i) using 1; ext t y l; simp only [Finset.prod_apply];apply Finset.prod_congr rfl; intro i _; change (f i t y l) ^(n i)/(n i).factorial= e i*_; simp only [Pi.pow_apply]; unfold e; ring
    exact Bed.casket _
lemma markPoke (u:ℕ){R':RG.Rep G f}(Y:Cash W x μ L Q o C T R')(D:Match.Alliance Y H 1 0): Bed b (fun s:sun=>fun y p' => Palette.shoot (p s) H χ Cy Y D y p' u U):=by
   unfold Palette.shoot Palette.shootK; by_cases he: u∈Set.range (Refrain.visa Y D)
   · obtain ⟨i,rfl⟩:=he; simp_rw [Progress.DirectedRecipe.stuffed]; exact Tier.markFete H h U Cy χ _
   simp_rw [Progress.DirectedRecipe.blank _ _ he]; exact Bed.casket _
end Tier
end YM.FullVolume.Ray
