import YM.FullVolume.Poesy.Blush
/-! E6 Layout steps full volume.Epoch. Keep Records by exact tags.Canvas.Read.F. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
open Matrix Window Progress.StationaryScenes Green Census Control Flux FullVolume.Shadow
open Gate Frond Vine Mask
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{J: Ultrafilter ℕ}{Q:ConnectedActivityE6.Target G P}{W x μ C₀ a b e ℓ v :ℝ}{o:Target.Order G W}
    {Λ: Era G S}{U:ℕ→ E→ Config G c}{Z: Draft F G} {K H:ℕ→ Epoch Λ}{j:ℕ}{p:E}
open FullVolume.Neptune Flux Shield Eider Packets Polar
namespace Yard
variable {ι κ:Type}{X Y:Support c}{B:BudgetPoint} {x y:Site c}
structure Rich (B:BudgetPoint)(x:Site c)(X:Support c)(F:ℕ→ Config G c→ℝ):Prop where
     smooth :∀ n,B.Regular X (F n)
     sharp: ∃ C,∀ n,B.supBounds x X (F n) C
structure Loom (B:BudgetPoint)(x:Site c)(X:Support c)(F H:ℕ→ Config G c→ℝ):Prop where
    a: Rich B x X F
    b: Rich B x X H
    gaze :∀ i> (0:ℝ),∀ᶠ n in atTop,B.supBounds x X (F n-H n) i
variable {F Gf H P':ℕ→ Config G c→ℝ}
lemma many {F H:ℕ→ι→ Config G c→ℝ}{A:ι→ RegularAddress c}(h:Canopy B A F H) (i): Loom B (A i).site (A i).support (fun n=>F n i) (fun n=>H n i):=by
   have hx {F:ℕ→ι→ Config G c→ℝ}(h:PulseWise B A F):Rich B (A i).site (A i).support (fun n=> F n i):=by
       obtain ⟨w,hw,H⟩:=h.sup; exact ⟨fun n=>h.chart ..,_,fun n=> VerifiedReset.sup_le (H ..) (budget_single (hw.bound.choose_spec n) i)⟩
   exact ⟨hx h.a,hx h.b,h.sails _⟩
lemma cues {F H:ℕ→ι→ Config G c→ℝ}[Fintype ι]{A:ι→RegularAddress c}(h:∀ i,Loom B (A i).site (A i).support (fun n=> F n i) (fun n=> H n i)):Canopy B A F H:=by
   have hv {F:ℕ→ι→ Config G c→ℝ}(h:∀ i,Rich B (A i).site (A i).support (fun n=> F n i)):PulseWise B A F:=by
       choose f hf using fun i=> (h i).sharp; exact ⟨fun n i=> (h i).smooth n,_, Sparse.constant (hasSum_fintype f).summable (fun i=> (hf i 0).1),fun n i=>hf i n⟩
   exact ⟨hv fun i=>(h i).a,hv fun i=>(h i).b,fun i=>(h i).gaze⟩
lemma Loom.minus (h:Loom B x X F H)(hp:Loom B x X Gf P'): Loom B x X (F-Gf) (H-P') :=by
    have ht {F H:ℕ→ Config G c→ℝ}(ha:Rich B x X F)(hb:Rich B x X H) : Rich B x X (F-H):= ⟨fun i=> VerifiedReset.reg_sub (ha.smooth i) (hb.smooth i),_,fun i=> CouplingShape.sup_sub (ha.smooth i) (hb.smooth i) (ha.sharp.choose_spec i) (hb.sharp.choose_spec i)⟩
    refine ⟨ht h.a hp.a, ht h.b hp.b,fun e he=>?_⟩; filter_upwards [h.gaze _ (half_pos he),hp.gaze _ (half_pos he)] with n hn hh
    change B.supBounds x X ((F n-Gf n)-(H n-P' n)) _
    rw [show _-_=(F n-H n)-(Gf n-P' n) from (show (F n-Gf n)-(H n-P' n)=_ from by abel)]
    exact VerifiedReset.sup_le (CouplingShape.sup_sub (ht h.a h.b|>.smooth n) (ht hp.a hp.b|>.smooth n) hn hh) (add_halves e).le
lemma Loom.zero: Loom B x X (0:ℕ→ Config G c→ℝ) 0:=by
   let z:Rich B x X (0:ℕ→ Config G c→ℝ):= ⟨fun n=> CouplingShape.reg_const _, _,fun n=>CouplingShape.sup_const _⟩
   refine ⟨z,z,fun i hi=>Eventually.of_forall fun n=>?_⟩; change B.supBounds _ _ ((0:Config G c→ℝ)-0) _; rw [sub_zero]; exact VerifiedReset.sup_le (CouplingShape.sup_const (0:ℝ)) (by simpa using hi.le)
lemma Loom.seats (h:Loom B x X F H) (a:ℝ) : Loom B x X (a • F) (a • H):=by
    have hp {F:ℕ→ Config G c→ℝ}(h:Rich B x X F): Rich B x X (a • F):= ⟨fun i=>CouplingShape.reg_scale _ (h.smooth i),_,fun i=>CouplingShape.sup_scale _ (h.sharp.choose_spec i)⟩
    refine ⟨hp h.a,hp h.b,fun e he=>?_⟩; by_cases hv:a=0
    · subst a; rw [zero_smul, zero_smul]; exact Loom.zero.gaze _ he
    have hv:=abs_pos.mpr hv; filter_upwards [h.gaze _ (div_pos he hv)] with i hi; dsimp only [Pi.smul_apply]; rw [← smul_sub]; exact VerifiedReset.sup_le (CouplingShape.sup_scale _ hi) (le_of_eq (by field_simp)) -- lemma name
lemma Loom.tuck (h:Loom B x X F H)(hp:Loom B x X Gf P'): Loom B x X (F+Gf) (H+P'):=by
    have hh:= h.minus (hp.seats (-1)); simpa only [neg_one_smul, sub_neg_eq_add] using hh
lemma Loom.tall (s: Finset ι){F H:ℕ→ι→ Config G c→ℝ}(h:∀ i∈s,Loom B x X (fun n=> F n i) (fun n=> H n i)): Loom B x X (fun n=>∑ i∈s,F n i) (fun n=>∑ i∈s,H n i):=by
    induction s using Finset.induction_on with
    | empty=>simp; exact Loom.zero
    | insert i s hi ih=> simp_rw [sum_insert hi]; exact (h i (mem_insert_self ..)).tuck (ih fun j hk=> h j (mem_insert_of_mem hk))
lemma Loom.moves (h:Loom B x X F H)(i:Site c)(Y:Support c)(hf:X⊆Y): Loom B i Y F H:=by
   obtain ⟨v,hv,V⟩:= Meadow.supHeight (G:=G) (n:=c) B; have he :=zero_lt_one.trans_le hv
   have ht {F:ℕ→ Config G c→ℝ}(h:Rich B x X F):Rich B i Y F:= ⟨fun n=>CouplingShape.reg_extend (h.smooth n) hf, _,fun n=>CouplingShape.sup_extend (V x i X _ (h.smooth n) _ (h.sharp.choose_spec n)) hf⟩
   refine ⟨ht h.a,ht h.b,fun t hy=>?_⟩; filter_upwards [h.gaze _ (div_pos hy he)] with n hn
   exact VerifiedReset.sup_le (CouplingShape.sup_extend (V x i X _ (VerifiedReset.reg_sub (h.a.smooth n) (h.b.smooth n)) _ hn) hf) (Eq.le (by field_simp))
lemma Loom.shirt (h:Loom B x X F H) (f g:ℕ→Prop)(hf:∀ᶠ i in atTop,f i ↔ g i): Loom B x X (fun n=> if f n then F n else 0) (fun n=> if g n then H n else 0):=by
   have ht {F:ℕ→ Config G c→ℝ}(h:Rich B x X F) (g:ℕ→Prop): Rich B x X (fun n=>if g n then F n else 0):=by
       obtain ⟨C,hp⟩:=h.sharp; have he:0≤C:=(hp 0).1; constructor
       · intro i; split; · exact h.smooth i
         exact CouplingShape.reg_const _
       refine ⟨C,fun n=>?_⟩; split; exact hp n
       exact CouplingShape.sup_larger (CouplingShape.sup_const 0) (by simpa using he)
   refine ⟨ht h.a f,ht h.b g,fun b hb=>?_⟩; filter_upwards [h.gaze b hb,hf] with n hn hv'; simp_rw [hv']; split; exact hn
   rw [sub_zero]; exact CouplingShape.sup_larger (CouplingShape.sup_const 0) (by simpa using hb.le)
lemma Loom.still (h:Loom B x X F H): Loom B x X (fun i=>Boulevard.stillA (F i)) (fun i=> Boulevard.stillA (H i)):=by
   let V(F:ℕ→ Config G c→ℝ) (n:ℕ) (_:Config G c):= F n 1; have he {F:ℕ→ Config G c→ℝ}(h:Rich B x X F): Rich B x X (V F):=⟨fun i=> CouplingShape.reg_const _,_,fun i=> VerifiedReset.sup_le (CouplingShape.sup_const (F i 1)) ((h.sharp.choose_spec i).2 1 (CouplingShape.clear_one B X) [] (Nat.zero_le _) (by simp))⟩
   refine h.minus (Gf:=V F) (P':=V H) ⟨he h.a,he h.b,fun i hi=>(h.gaze i hi).mono ?_⟩
   exact fun n hn=> VerifiedReset.sup_le (CouplingShape.sup_const _) (hn.2 1 (CouplingShape.clear_one B X) [] (Nat.zero_le _) (by simp))
end Yard
end YM.ConnectedActivityE6.Lim
