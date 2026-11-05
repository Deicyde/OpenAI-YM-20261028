import YM.RG08.Weald.Pitch
import YM.RG08.Quarry.Quires

/-!
# Operandi with arbitrary cochains (sparse) on cover, BEFORE resets.
All h,e positive, no estimate used; exhibits literal form of Ward inputs needed
for deterministic triangular cancellation. G.Lie τ. Price in accompanied grow
checkpoint.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Weald
open Jetty Skiff Lattice Isles Forms Pert.Bulk Function Finset Laurent Filter Packets Steam Mount
open Room Gallery Camera MvPolynomial Glyph Hatch Quarry
open RG Wilson Stationary Precision Tack Tree Prism Slate Work.F05
open scoped Topology BigOperators ENNReal Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {I J:Type}{n d l t:ℕ}{σ C:ℝ}{h:0<σ}

abbrev StringLg (P:Pack n (Market I))(U:Span n I):=∀ f x,Tendsto (fun i=>U i (port (Isles.chain i) ∘ x) f) atTop (𝓝 (P x f))
private lemma ashen {P:Pack n (Market I)}{U:Span n I}(f:Pearl)(hs:StringLg P U)(v:Gallery.Tray (Market I))(e:ℕ):
   Tendsto (fun i=>tap e (summit (U i) f (Gallery.native _ v))) atTop (𝓝 (tap e (summit P f v))):=by
 let S:=v.base; let s:=desks S n
 have he (Q:Side) : s.image (fun x=> port Q ∘ x)=desks ((Gallery.native Q v).base) n:=by
    ext x; simp only [s,desks,Fintype.mem_piFinset,Finset.mem_image]; constructor
    · rintro ⟨y,hy,rfl⟩ j;exact Finset.mem_image_of_mem _ (hy _)
    intro H;choose t ht hh using fun j:Fin n=> Finset.mem_image.mp (H j: x j∈_)
    exact ⟨t,ht,funext hh⟩
 have hg : ∀ᶠ i:ℕ in atTop, tap e (summit (U i) f (Gallery.native _ v))=∑ y∈s,U i (port (Isles.chain i) ∘ y) f*tap e (fret v.get y):=by
    filter_upwards [Gallery.moving (N:=Isles.chain) Isles.rise S] with i hi
    let Q:= Isles.chain i
    unfold summit Gallery.volume;rw [show desks (I:=Isles.colony I i) (Gallery.native Q v).base n = s.image (fun a=> port Q ∘ a) from (he Q).symm]
    let UH:Tape n (Cove Q I)→Dig:=fun x=> during f (U i) x • fret (Gallery.native Q v).get x
    change tap e ((s.image (fun a=>port Q ∘ a)).sum UH)=_
    rw [Finset.sum_image (fun a ha b hb hab=> _root_.funext fun j=>?_)]
    · unfold tap during;rw [map_sum];apply sum_congr rfl;intro y hy;rw [PowerSeries.coeff_smul,smul_eq_mul];congr 2; unfold fret;apply prod_congr rfl;intro j _;change v.get (reach (port Q (y j)))=_; rw [hi _ (Fintype.mem_piFinset.mp hy j)]
    exact ((hi _ (Fintype.mem_piFinset.mp ha j)).symm.trans (congrArg (reach (I:=I)) (congrFun hab j))).trans (hi _ (Fintype.mem_piFinset.mp hb j))
 rw [summit,Gallery.volume,tap,map_sum];simp_rw [PowerSeries.coeff_smul,smul_eq_mul]
 refine Tendsto.congr' (hg.mono (fun _ h=>h.symm)) (tendsto_finsetSum _ (fun x _=> (hs f x).mul_const _))

lemma ascribed {P:GrainS (Market I)}{U:(i:ℕ)→GrainS (colony I i)}(v:Gallery.Tray (Market I))(f:Pearl)(e:ℕ)
   (H:formal P U d h e): Tendsto (fun i=>tap e (mint l (U i) f (Gallery.native _ v))) atTop (𝓝 (tap e (mint l P f v))):=by
 simp_rw [tap,mint,PowerSeries.coeff_mk,crown,map_sum];refine tendsto_finsetSum _ fun b hb=> tendsto_finsetSum _ fun n _=>?_
 obtain ⟨C,h⟩:=H b (by simpa [Nat.lt_succ_iff] using hb) n
 exact ashen f h.front v (e-b)

-- bound inputs in any stage before hood.
def Growth (d:ℕ)(P:GrainS (Market I)):=∀ e n,Lyrics (P e n)∧∃ (σ:ℝ)(h:0<σ)(B:ℝ), 0 ≤ B ∧ Sings (stance I) d h (P e n) B
lemma Growth.pops {M:GrainS (Market I)}(H:Growth d M):Pops M:=fun i n=>by obtain ⟨h,σ,hσ,b,_hb,H⟩:=H i n; exact ⟨h,stance I,d,σ,hσ,b,H⟩
lemma Growth.license {M:GrainS (Market I)}(H:Growth d M)(hM:Lit l M)(e:ℕ):∃ (σ:ℝ)(h:0<σ)(C:ℝ),0≤C ∧ ∀ k≤e,∀ n,Sings (stance I) d h (M k n) C:=by
 choose a hA b hB B using fun x:ℕ×ℕ=> (H x.1 x.2).2
 let s:=range (e+1)×ˢ range (l+e+1)
 obtain ⟨σ,p,h,hp,hh⟩:= docket s a b (fun i _=>hA i) (fun i _=>hB i)
 refine ⟨σ,h,p,hp,fun k hk n=>?_⟩
 by_cases hn:M k n=0; · rw [hn];exact tin
 obtain ⟨ht,hy⟩:= hh (k,n) (Finset.mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (Nat.lt_succ_iff.mpr ((hM k n hn).trans (by omega)))⟩)
 exact (B (k,n)).mono ht le_rfl (fun _=>le_rfl) hy

section
variable {G:Gauge}(P:Patch)(K:KernelChoices)(A B:Bed)(C:Castle G)(Z:ChartRatio G)

def vessel (H:P.Branches K G)(l:ℕ)(M:GrainS (Market (Tack.Head P G))):GrainS (Market (Loc G 1)):= Trickle.mouth (Prism.rains P K A) (Skiff.spin l (Prism.ice P K A) (inlet H C Z) M 1)
def weldF (N:Side)(H:P.Branches K G)(l:ℕ)(M:GrainS (Market (Tack.Head P G))):GrainS (Lines G N 1) := Trickle.mouth (springGreen P K A N) (Skiff.spin l (winterGreen P K A N) (unveil (inlet H C Z) N) (Weald.raft _ M N) 1)

-- def above choose Cove notation
lemma won (H:P.Branches K G)(M:GrainS (Market (Tack.Head P G)))(hM:Growth d M)(hY:Lit l M)
    (hc:Mount.Stable C){p:ℝ}(hw:Cell.Warm G K P A σ p)(hp:0<σ)(hn:σ ≤ 1)(e:ℕ):
   ∃ (τ:ℝ)(k:0<τ),formal (vessel P K A C Z H l M) (fun j=>weldF P K A C Z (Isles.chain j) H l M) d k e:=by
 let X:=inlet H C Z
 have hE:= inlet_eligible H Z hc
 have hS i:slaw X i:=by
    by_cases hy:0< i
    · have hd:= ((castle_room P C hc i).add (bell_room H i)).neg.add (dusk_room P Z i)
      intro n;convert hd n using 1; rw [show X i n=ghost H C Z i n by unfold X inlet;rw [if_pos hy]];rfl
    intro n;refine ⟨1,0,zero_lt_one,le_rfl,?_⟩;unfold X inlet; rw [if_neg hy];exact zero_held
 obtain ⟨α,hα,hA⟩:=hedgeline X e hE (legal_inlet H Z hc) hS
 obtain ⟨μ,hμ,Q,hQ,hq⟩:=hM.license hY e
 let τ:=min σ (min α μ)
 have k:0<τ:=lt_min hp (lt_min hα hμ)
 have hk :τ≤α:=(min_le_right ..).trans (min_le_left ..); have hh:τ≤μ:=(min_le_right ..).trans (min_le_right ..)
 have ht: Hatch.shut e X (fun i=>unveil X (Isles.chain i)) τ:=⟨fun i n=>by
    obtain ⟨B,hB⟩:=hA i n; refine ⟨B,?_⟩;convert (hB.mono k hk le_rfl) using 1; funext j
    change hedge e (unveil X (Isles.chain j)) i n=unveil (hedge e X) (Isles.chain j) i n;rw [hedge_unveil]⟩
 obtain ⟨hL,hP⟩:=ready_roads P K A hw hp hn
 have hiM:formal M (fun j=>Weald.raft _ M (Isles.chain j)) d k e:=fun i hi n=>⟨Q,(Reed.sill (I:=Tack.Head P G) (hM i n).1 (hq i hi n) hQ).mono hh le_rfl le_rfl⟩
 exact ⟨_,k,coils ht (((Isles.tagged hL hp).mono k (min_le_left ..) le_rfl).line) hiM l (1:ℝ) ((Isles.tagged hP hp).mono k (min_le_left ..) le_rfl)⟩

variable (o:Site P.L){M:GrainS (Ed G Cover)}
lemma braids (he:Lit l M):Lit l (plank P o M):=fun i n h=>he i n (fun hz=> h (by unfold plank;rw [hz,Hatch.dead]))
lemma braised {M:GrainS (Market (Tack.Head P G))}(he:Lit l M)(c:Side):Lit l (Weald.raft _ M c):=fun e n h=>he e n (fun hz=>h (by unfold Weald.raft;rw [hz,Hatch.dead]))
lemma grip (ht:Growth d M):Growth d (plank P o M):=by
 intro e n
 obtain ⟨he,σ,h,p,hp,hs⟩:=ht e n
 refine ⟨Hatch.cull (door P o) he hs,σ,h,Real.exp (σ*12)*p,mul_nonneg (Real.exp_pos _).le hp,?_⟩
 apply b_afford (door P o) (step_door ..) h le_rfl (mul_nonneg h.le (by norm_num)) _ hs
 intro j; change σ*abroad _≤σ*abroad j+_; rw [←mul_add]; apply mul_le_mul_of_nonneg_left _ h.le
 refine (height_door P o j).trans ?_; gcongr; exact div_le_self (abroad_nn _) (Nat.one_le_cast.mpr P.L.property)

end
end YM.RG08.Weald
