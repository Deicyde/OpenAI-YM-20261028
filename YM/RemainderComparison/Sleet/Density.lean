import YM.RemainderComparison.Sleet.Flint
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Sleet
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling Raw Itinerary Opacity Cascade Lyric Daisy Halo Height
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι]
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J:ℕ}(χ:Chi)
variable (N: Captain H j q d v u A b r B e n χ) (Ξ:Utopia H j v d r q χ)
variable (l:ι→ℝ) {T' S' δ B' b' τ ε:ℝ}
local notation "D" => grow G L x
local notation "V'" => Q.costs L μ R.beta x q
local notation "LT" => Mixed.lengths S V' (ConnectedActivityE6.lengths T R)
local notation "Z" => radiusB x


open Deck
-- Clean supports fit fixed κ-native balls. Crop upon output migration.
-- No identification of unaffected E-origin using crest alone.
local notation "U₀" => region k s
variable (z:H.fragrances) (w : Syllable M H z)
lemma key_roof (Y:ℕ)(i:ℕ)(h:¬cloudy R Y i) :
    H.supportP (Opacity.key S i)⊆ neighbors (Mint.width Q.halo Z Y) (S.ratio.parent (R.activities.reg i).site):=by
  let p:= R.activities.reg i; have he: 0<Z:= by have he:= H.laws.data.room.sight.1; omega
  intro a ha
  change a∈ enlargement S.ratio Q.halo Z (inspected p.support) at ha
  obtain ⟨w,hw,hz⟩:= halo_spec.mp (inspected_price S.ratio Q.halo Z p.support he ha); obtain ⟨w,h',rfl⟩:=mem_image.mp hw; apply (neighbors_mem ..).2
  have hh: separation p.site w ≤ Y:=not_not.mp (fun he=>h ⟨w,h',he⟩)
  have hp:= Work.E04.parent_separation S.ratio p.site w
  apply (separation_triangle _ (S.ratio.parent w) a).trans; unfold Mint.width; nlinarith only [he,hp,hz,hh]
lemma cap_one (X:Support c)(i:Site c)(b:ℕ)(h:X⊆ neighbors b i): coverNumber b X≤1:=by
   have he:neighbors b i=halo b ({i}:Finset _):= by ext j; simp only [halo_spec,neighbors_mem]; simp
   exact (Corona.list_cost _ (show covers b X {i} from ⟨he ▸ h, Corona.ship_halo _ (fun j hj k hk=>by rw [mem_singleton.mp hj,mem_singleton.mp hk])⟩)).trans_eq (card_singleton _)
variable (E:Set ℕ)
variable {V:Config G c} {Y:ℕ}
-- upon tally, prepare Holds under Z.chart. no oracle smaller than indicator.
structure Nordic (E:Set ℕ) (k s Y:ℕ) : Prop where
   core : Beacon.core H z (region k s) (Pressure.Stores.till x)
   birds i j : j∈ (z.2 i).val\ (w i).reach → (∃ j':Mint.Music c f, j=Mint.disc S j' ∧ Mint.verse R.path j' ≤ radiusB x) ∨ ∃ n:ℕ,n∉ E ∧ ¬cloudy R Y n∧ j=Opacity.key S n
   anchors i : i∈page M H z w → ∃ j, (M i).turn=Wing.logKey j∧ ¬cloudy R Y j∧(M i).crest.image S.ratio.parent ⊆ reachability z
   port : coverNumber (Mint.width Q.halo (radiusB x) (radiusB x+Y)) (reachability z) ≤ region k s
omit [Fintype ι] in
lemma season (he:string M H χ z w V≠0) (_hp: ¬muddy R Y M (page M H z w))(hx: ¬Flurry H z k s) (hz:¬ tumble H z)(hI:¬ Halo.dyed M H (ridge R Y E) z w)(hE:¬ Halo.dyed M H E z w) :
    Nordic M H z w E k s Y:= by
  have ht:= Lyric.listens M H χ z w V he (show ¬ Storm H k s z from fun ht=>hx (Or.imp_right (Or.imp_right fun h=> (within x L).trans h) ht))
  obtain ⟨hv,hg,hxL⟩:= grown M H χ z w V he
  have hA (j)(i)(hi : i∈(z.2 j).val\(w j).reach): (∃ p:Mint.Music c f, i=Mint.disc S p∧Mint.verse R.path p≤Z) ∨ ∃ n:ℕ,n∉ E∧¬cloudy R Y n∧i=Opacity.key S n:=by
    rcases mood M H χ z w i (mem_sdiff.mp hi).1 he hx hz with ⟨i,rfl,h⟩|⟨i,rfl⟩
    · exact Or.inl ⟨i,rfl,h⟩
    have h : i∉ E := fun h=> hE ⟨j,_,⟨i,h,rfl⟩,hi⟩
    exact Or.inr ⟨i,h,fun hi'=> hI ⟨j,_,⟨i,⟨h,hi'⟩,rfl⟩,hi⟩,rfl⟩
  have hb (i) (hi:i∈page M H z w): ∃ j,(M i).turn= Wing.logKey j∧¬cloudy R Y j∧(M i).crest.image S.ratio.parent⊆reachability z:=by
    have hm:= hxL i hi
    have he:¬ shade R Y (M i).turn:= fun h=> _hp ⟨i,hi,h⟩
    obtain ⟨a,ha,hp⟩:= mem_biUnion.mp hi
    have hs := (hg a).2.2 ((w a).reaches_of hp)
    unfold Palette.sign at hs
    cases ht':(M i).turn with
    | logKey j=> exact ⟨_,rfl,by rw [ht'] at he; exact he,hm⟩
    | gasKey j=> rw [ht'] at hs; have hw:j∈ own (z.2 a).val:= mem_toLeft.mpr (mem_toRight.mpr hs); rw [(ht.4 a).2.2.2] at hw; simp at hw
  let p':= Mint.width Q.halo Z (Z+Y); refine ⟨ht,hA,hb,?_⟩
  have hL j i (hi:i∈(z.2 j).val): coverNumber p' (H.supportP i)≤1:= by
    by_cases he:i∈(w j).reach
    · obtain ⟨i,hh,rfl⟩:= mem_image.mp he; obtain ⟨n,hn,h,-⟩:= hb i (mem_biUnion.mpr ⟨_,mem_univ j,hh⟩)
      unfold Palette.sign; rw [hn]; apply cap_one (i:=S.ratio.parent (R.activities.reg n).site); apply (key_roof H _ n h).trans; unfold p' Mint.width; intro a ha; exact (neighbors_mem ..).2 ((neighbors_mem ..|>.1 ha).trans (by omega))
    rcases hA j i (mem_sdiff.mpr ⟨hi,he⟩) with ⟨p,rfl,hp⟩|⟨p,-,h,rfl⟩
    · exact cap_one _ _ _ (Mint.centered Q.halo Z (Z+Y) (by have h:= H.laws.data.room.sight.1; omega) _ S T R (hp.trans (Nat.le_add_right ..))).2
    apply cap_one _ _ _ ; refine (key_roof H _ p h).trans ?_; unfold p' Mint.width; intro a ha; exact (neighbors_mem ..).2 ((neighbors_mem ..|>.1 ha).trans (by omega))
  have hh(z':Option (Fin z.1)) : coverNumber p' (H.smallAt (z.2 z'))≤ (z.2 z').val.card:= (Ac.cover _ _ (hg _).1).trans (by simpa using Finset.sum_le_sum (s:=(z.2 z').val) (g:=fun _=>1) (fun i hi=> hL z' i hi))
  have hp := connected_pay H.seam H.smallAt p' H.testS z.2 zero_le_one hv
  unfold Trees.currency at hp; simp_rw [one_mul,← Real.exp_sum,Real.exp_le_exp] at hp
  have hu := ht.arity; have he₁ : coverNumber p' (reachability z) ≤ breadth H z:= by exact_mod_cast (hp.trans (Finset.sum_le_sum (fun i _=> show (coverNumber p' (H.smallAt (z.2 i)):ℝ) ≤ (((z.2 i).val).card:ℝ) from by exact_mod_cast hh i)))
  exact he₁.trans (le_trans (Nat.le_add_left ..) (show degree H z ≤ region k s from hu.le))

def cortex (l b:ℕ)(k s μ:ℕ):ℕ:= (region k s) * (4*Mint.width l b (b+μ*b)+2)+2*Mint.width l b (b+μ*b)
lemma cortex_p {l b p':ℕ}(he:1≤ b): cortex l b k s p' ≤ cortex l 1 k s p' * b:=by
   unfold cortex Mint.width
   generalize region k s = n
   nlinarith only [he,Nat.zero_le n,Nat.zero_le l,Nat.zero_le p',Nat.mul_le_mul_left n he]
omit [Fintype ι] in
lemma plate {p:ℕ} (hh:Nordic M H z w E k s (p*Z))(y:Site c) (hy:y∈reachability z) : reachability z⊆ neighbors (cortex Q.halo Z k s p) y:= by
   intro i hi; apply (neighbors_mem ..).2
   exact (Corona.extent (reachability z) (Mint.width Q.halo Z (Z+p*Z)) hy hi).trans (by unfold cortex; gcongr; exact hh.port)
end YM.RemainderComparison.Sleet
