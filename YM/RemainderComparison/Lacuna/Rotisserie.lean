import YM.RemainderComparison.Lacuna.Bubbles
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Lacuna
open Function Filter Finset Lattice RG Wilson MeasureTheory ProbabilityTheory Ovens
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Work.E03 Work.F03
open PhysicalNext PhysicalNext.Repeat Song Slide Trio
open AnalyticBridge VerifiedReset Collection Quotes YM.Extra.Iteration
open Mosaic Mosaic.Verse WickReps Flues Lobby
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c:Side}{ι β I : Type}{α:Type*}[DecidableEq β]
open Vesuvius Jolt
-- Cap petals Glow orientation.Read B rates keep all.Inspects.Final.B.Same
variable (S:Vesuvius G c ι I α) (P:BudgetPoint)(u:Set ι)(a b:α)(roots:ι→Support c)
local notation "Tv"=> Lacuna.shade S u
local notation "P₀" => Jolt.standing c
local notation "F₁" => Seat c× I
local notation "Tt"=> Lacuna.bubbles S u a
local notation "L₁"=> Seat c
local notation "Ω"=> Lacuna.shade Tt u
variable {σ v d:ℝ}
variable (U:Config G c)
open Marker
-- orientation readiness of soft.density
lemma magma {s:Signed}{t:Site c} (p:F₁) (b:α):
    let z:= Song.whirl s t p
    (p∈ Lacuna.shade Tt u ↔ z∈ Lacuna.shade Tt u)∧ (Tt).site z=((Tt).site p).image (affine s t)∧ (p∈ Lacuna.shade Tt u → (Tt).log b z U=(Tt).log b p (pull s t U)):=by
   obtain ⟨x,i⟩:=p; intro z; have hv:=gleam S u a
   refine ⟨(hv ..).trans (hv (Seat.move s t x) i).symm, Seat.spread_move .., fun h=>?_⟩
   have ht:= (hv ..).1 h; change (Tt).log b (Seat.move s t x,i) _= _; rw [Lacuna.presence S u a b ht,Lacuna.presence S u a b ht,Seat.view_move]; rfl
-- σ arbitrary.Chosen.A
lemma sputum (h:S.Works P roots u σ v d)(hv:0≤ σ) : wray Tt u b U = revolves (fun x=> wray S u a (x.view U)):=by
    let e (x:L₁× ↑Tv) : ↥Ω:=⟨(x.fst,x.snd.val), (gleam S u a ..).mpr x.snd.prop⟩
    have he : Bijective e:= by
       refine ⟨fun i j h=> ?_ ,?_⟩
       · have hh:(i.1,i.2.1)=(j.1,j.2.1):= congr_arg Subtype.val h
         exact Prod.ext (congr_arg (Prod.fst (α:=L₁) (β:=I)) hh) (Subtype.ext (congr_arg (Prod.snd (α:=L₁) (β:=I)) hh))
       rintro ⟨⟨x,i⟩,h⟩; exact ⟨(x,⟨i,(gleam S u a x i).mp h⟩),rfl⟩
    let g V (p:↥Tv):= S.log a p.val V
    let f (p:↥Ω) := (Tt).log b p.val U
    have hp t : HasSum (fun i: Tv=> f (e (t,i))) (Rim c *(wray S u a (t.view U))):=by
        refine (((barm P S h hv a (t.view U)).hasSum).mul_left (Rim c)).congr_fun fun i=>?_ ; change (Tt).log b (t,i.val) _= _; rw [Lacuna.presence S u a b i.prop]; rfl
    have ht := (ConnectedActivityE6.Raw.finite_start (fun x=> f (e x)) _ hp); unfold Lacuna.revolves; rw [Finset.mul_sum]; exact ((Equiv.ofBijective e he).tsum_eq _).symm.trans ht.tsum_eq
variable {J:Census β}(z:ι→ Marker.Poly J)
lemma shards : Lacuna.mark Tt u z b U= Lacuna.mark S u z b U:=by
    let f i: ↑(Ωᶜ):= ⟨(P₀,(i: ↑(Tvᶜ)).val), mt (gleam S u a P₀ _).1 i.prop⟩
    let e: ↑(Tvᶜ) ↪ ↑(Ωᶜ):= ⟨f,fun i j h=> Subtype.ext (congr_arg (fun i: ↑(Ωᶜ)=> i.val.2) h)⟩
    refine Progress.DirectedRecipe.transferred_sum e (fun j=>?_ ) ?_
    · change Vesuvius.books b u z Tt U (P₀,j.val)= _; unfold Vesuvius.books; rw [show (Tt).log b (P₀,j.val)=S.log b j.val from (if_neg j.prop).trans (if_pos rfl),show (Tt).opus (P₀,j.val)= S.opus j.val from if_neg j.prop]
    rintro ⟨⟨x,i⟩,h⟩ he; have ht: i∉ Tv:= mt (gleam S u a x _|>.2) h
    have hp : x≠P₀:= by rintro rfl; exact he ⟨⟨i,ht⟩,rfl⟩
    change Vesuvius.books b u z Tt U (x,i)=0; unfold Vesuvius.books; rw [show (Tt).log b (x,i)=0 from (if_neg ht).trans (if_neg hp)]; simp
section wiring
variable [Countable I]
open Progress.DirectedRecipe Marker Serif
-- pad soft onto ℕ but need WHIRLS. Insert another copy, and index codec.
abbrev extras(c:Side)(I:Type):= (Seat c× I) ⊕ (Seat c× ℕ)
def coder(c:Side)(I:Type)[Countable I]: ℕ≃ extras c I:= YM.Extra.Iteration.numbering _
def plugs (c:Side): (Seat c× I) ↪ ℕ:= Function.Embedding.inl.trans (coder c I).symm.toEmbedding
local notation "Eʼ"=> coder c I
local notation "Pʼ"=> plugs (I:=I) c

def rudder : Scone ι α G c where
    leg i:= Sum.elim (Tt).site (fun x=> x.1.spread {0}) (coder c I i)
    rest i:=by cases coder c I i with
               | inl p=> exact (Tt).yeah p
               | inr p=> exact (singleton_nonempty (0:Site c)).image _
    glyph := Progress.DirectedRecipe.stuff (plugs c) (Tt).opus
    glow b:= Progress.DirectedRecipe.stuff (plugs c) ((Tt).log b)
-- * threshold p k still not post projection.
local notation "L"=> Lacuna.rudder S u a
lemma pilot (i:F₁) : (L).leg (Pʼ i)=(Tt).site i:=congr_arg (Sum.elim _ _) ((Eʼ).apply_symm_apply _)
lemma feeds {p:ℕ}(h:S.Works P roots u σ v d): (L).Rises P roots∧ (L).Treasures u p P.B σ v d:=by
    have hx:= Lacuna.spools S P u a roots h; have hp i : (L).leg (Pʼ i)=(Tt).site i:= pilot S u a i
    have hl i : (L).glyph (Pʼ i)=(Tt).opus i := Progress.DirectedRecipe.stuffed Pʼ _ _
    have hg b i : (L).glow b (Pʼ i)= (Tt).log b i:= Progress.DirectedRecipe.stuffed Pʼ _ _
    have hb b (i:ℕ)(hi:i∉ Set.range Pʼ) : (L).glow b i=0:= Progress.DirectedRecipe.blank Pʼ _ hi
    have he i b:Tidy P ((L).leg i) ((L).glow b i)∧ Flues.apex roots ((L).leg i) ((L).glyph i) ((L).glow b i)∧ ∀ U, Healthy P.threshold ((L).leg i) U→ (L).glow b i U=0:=by
       by_cases hm:i∈ Set.range Pʼ
       · obtain ⟨i,rfl⟩:=hm; rw [hp,hg,hl]; exact ⟨hx.oasis i b,hx.quest i b,hx.happy i b⟩
       rw [hb _ _ hm]; exact ⟨Trio.tidy_const P _,fun _ _ _ hh=> (hh rfl).elim,fun _ _=>rfl⟩
    obtain ⟨f,g,hf,hG,hv,hD,hV⟩:=hx.fortune
    refine ⟨⟨fun b i=>(he i b).1.uses,fun b i=>(he i b).1.borel,fun b i=>(he i b).1.invariant,fun i b=> (he i b).2.1,fun i b=> (he i b).2.2⟩,?_⟩
    refine ⟨stuff Pʼ f,stuff Pʼ g,Rack.positive _ _ hf,Rack.positive _ _ hG,fun i=> transfer_budget Pʼ (fun i=>by rw [hp,stuffed]) (fun i hi=>by rw [Progress.DirectedRecipe.blank _ _ hi]; simp) (hv i),fun i=>transfer_budget Pʼ (fun i=>by rw [hp,stuffed]) (fun i hi=>by rw [Progress.DirectedRecipe.blank _ _ hi]; simp) (hD i),fun i _ b U=> ?_⟩
    by_cases hm:i∈ Set.range Pʼ
    · obtain ⟨i,rfl⟩:=hm; rw [hl,hg,stuffed,stuffed]; exact hV ..
    rw [hb _ _ hm, Progress.DirectedRecipe.blank _ f hm,Progress.DirectedRecipe.blank _ g hm]; simp
lemma turns : Jolt.Whirls L u:=by
    have hp (i: Seat c×ℕ): (Eʼ).symm (Sum.inr i)∉ Set.range Pʼ:=fun ⟨j,h⟩=> Sum.inl_ne_inr (((Eʼ).symm.injective h) : Sum.inl j= Sum.inr i)
    have hh (s:L₁)(b:ℕ) : Jolt.dawn L u ((Eʼ).symm (Sum.inr (s,b))):=by
        unfold Jolt.dawn Verse.load; rw [show (L).glyph ((Eʼ).symm (Sum.inr (s,b)))=0 from Progress.DirectedRecipe.blank _ _ (hp _)]; simp
    have hD b i: (L).glow b ((Eʼ).symm (Sum.inr i))=0:=Progress.DirectedRecipe.blank _ _ (hp _)
    have hv i : Jolt.dawn L u (Pʼ i) ↔ i ∈ Lacuna.shade Tt u:=by unfold Jolt.dawn; rw [show (L).glyph _ = _ from Progress.DirectedRecipe.stuffed (Pʼ) (Tt).opus i]; rfl
    have hg b i : (L).glow b (Pʼ i)= (Tt).log b i:= Progress.DirectedRecipe.stuffed Pʼ _ _
    constructor
    · intro i hi b x; by_cases hm:i∈ Set.range Pʼ
      · obtain ⟨⟨y,i⟩,rfl⟩:=hm; have hf:= (gleam S u a ..).1 ((hv ..).mp hi); rw [hg,hg,Lacuna.presence S u a b hf,Lacuna.presence S u a x hf]
      rw [show (L).glow b i=0 from Progress.DirectedRecipe.blank _ _ hm,show (L).glow x i=0 from Progress.DirectedRecipe.blank _ _ hm]
    intro s b; let f:L₁ × I≃ L₁× I:= Song.whirl s b; let g:= Equiv.sumCongr f (Song.whirl (ι:=ℕ) s b); let l:= coder c I
    let B:= (l.trans g).trans l.symm; refine ⟨B,fun i=>?_⟩; obtain ⟨i,rfl⟩:= l.symm.surjective i
    rw [show B (l.symm i)=l.symm (g i) from congr_arg l.symm (congr_arg g (l.apply_symm_apply _))]; rcases i with i|⟨k,i⟩
    · have ht:= fun U=> Lacuna.magma S u a U (s:=s) (t:=b) i a -- edit b linder.read
      change (Jolt.dawn L u (Pʼ (f i))↔ Jolt.dawn L u (Pʼ i))∧ (L).leg (Pʼ (f i))= _ ∧ _
      refine ⟨(hv (f i)).trans (((ht 1).1).symm.trans ((hv i).symm)), by rw [pilot,show (L).leg (l.symm (Sum.inl i))= _ from pilot S u a i]; exact (ht 1).2.1, fun h U a'=>?_⟩
      change (L).glow a' (Pʼ (f i)) _ = (L).glow a' (Pʼ i) _; rw [hg,hg]; exact (Lacuna.magma S u a U (s:=s) (t:=b) i a').2.2 ((hv i).mp h)
    have ht j : (L).leg ((Eʼ).symm (Sum.inr j))= j.1.spread {0}:= by unfold Lacuna.rudder; simp
    exact ⟨iff_of_true (hh (Seat.move s b k) i) (hh k i), (ht (Seat.move s b k,i)).trans (((k.spread_move s b {0})).trans (congr_arg (fun x:Support _=> image _ x) (ht (k,i)).symm)),fun _ V b₀=> by
        change (L).glow b₀ ((Eʼ).symm (Sum.inr _)) _=(L).glow b₀ ((Eʼ).symm (Sum.inr _)) _; rw [hD,hD]; rfl⟩
variable (h:S.Works P roots u σ v d)(hx:0 ≤ σ) {gV:β→ℝ}{k:ℕ} (hZ:Serif.Chorus J gV u z k)
include h hx hZ
lemma flumes : HasSum ((L).plume u z b U) (tint J (Lacuna.revolves (fun i=> wray S u a (i.view U)))+ Lacuna.mark S u z b U):=by
    let A:= Vesuvius.books b u z Tt U; have hf:= Lacuna.spools S P u a roots h
    have hv := Vesuvius.pi_support P roots k b u z Tt hf hx hZ U
    rw [← Lacuna.sputum S P u a b roots U h hx,← Lacuna.shards S u a b U z,← Lacuna.farm P Tt z b U hf hx hZ]
    have he i : (L).plume u z b U (Pʼ i)= A i:=by unfold Scone.plume rudder; dsimp only; rw [Progress.DirectedRecipe.stuffed,stuffed]; rfl
    have hl i (hi : i∉ Set.range Pʼ): (L).plume u z b U i=0:=by unfold Scone.plume rudder; dsimp only; rw [Progress.DirectedRecipe.blank _ _ hi]; simp
    apply ((Pʼ).injective.hasSum_iff hl).1
    rw [show ((L).plume u z b U) ∘ Pʼ= A from funext he]; exact hv.hasSum
end wiring
end YM.RemainderComparison.Lacuna
