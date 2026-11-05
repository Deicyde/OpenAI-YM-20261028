import YM.RG08.Needle.Blip
/-!
# Affine/gauge path receipt on actual rooted mark. Doesn't require convergence
of witnesses. Funds strict tax ledger.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Needle
open RG Laurent Lattice Wilson Bloch Exterior Precision Push.AbsoluteSums Finset Function Filter Matrix Work.F08 Next.Free
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Shade Quire Source Source.Drops Labels Scores Scores.Pages Tall Vale Reflect Staffer Loom PertExtension.Series.Radial PertExtension.Series.Tested
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {I:Type}{G:Gauge}{p m c f L:Side}{v w R A B:ℝ}{D d e j r n i k t:ℕ}{τ:ℕ}{F:Labels.Frame G d}
variable {X Y:Cross L (Loc G 1) (Loc G 1)} {Z:Cross L (Candles G) (Loc G 1)} {U:BoardU D R G} {V W: EnvelopeU D R G j}
private def bow (V:EnvelopeU D R G r)(p:Site L) : EnvelopeU D R G r := fun i=>readdress (V i) p
private lemma bow_tid (ho: Odd L.val)(hp:1/2≤R)(hV:Tidy V)(p:Site L): Tidy (bow V p):=⟨rays_print hV.pens hp ho p,fun i j=> congr_arg (fun a=>readdress a p) (hV.woven i j)⟩
def rue (p : Site L)(Z:Cross L (Candles G) (Loc G 1))(U : EnvelopeU D R G j) (r:ℕ) : EnvelopeU D R G r := belly p Z (crock (bow U p) r)
lemma rue_paid (ho:Odd L.val)(hv:1/2≤R)(hp:Whole Z)(h:Tidy V)(p : Site L) : Tidy (rue p Z V r) := belly_mood p hp (crock_tid (bow_tid ho hv h p).pens _)
lemma rue_read (g:Ratio c f)(ho:Odd g.count.val)(hv:1/2≤R)(Z:Cross g.count (Candles G) (Loc G 1))(hp:Whole Z)(x:Site c)(p:Site g.count)(φ:Exam D)(hu:Tidy V)(u:Link G c):
    rootSong (plug φ R ∘ rue p Z V r) c x u=rootSong (crock (plug (roll (spinner p) (Carrier.unitStep g.count) φ) R ∘ V) r) f (g.assemble (x,p)) (installed g Z *ᵥ u) := by
  have hb:= bow_tid ho hv hu p; have ht:=crock_tid hb.pens r; unfold rue; rw [belly_sound _ _ hp ht]
  unfold rootSong Tensor.diagonal; rw [belly_period g p hp (Tidy.map _ ht),crock_map hb.pens _ _,show plug φ R ∘ bow V p= _ from (funext fun i=> (read_scores ho hv p _).2 φ : plug φ R ∘ bow V p=plug (roll (spinner p) (Carrier.unitStep g.count) φ) R∘V)]
lemma rue_empty (ho:Odd L.val)(hv:1/2≤R)(hp:Whole Z)(p:Site L): rue p Z (0:EnvelopeU D R G j) r=0 := by
  unfold rue bow; have he(u: Voice D R): readdress (0:Voice D R) p=0:= by unfold readdress; split <;> rfl
  rw [show (fun i=> readdress _ p)= _ from (funext fun i=> he 0:(fun i=> readdress ((0:EnvelopeU D R G j) i) p)=(0:EnvelopeU D R G j))]; unfold crock twistP tub; simp only [Pi.zero_apply,smul_zero, tsum_zero]
  rw [show sew (fun _=> 0)= (0:Rooted (Voice D R) (Candles G) r) from (by change sew 0=_; simpa using sew_sub (x:=(0:Rooted (Voice D R) (Candles G) r)) (y:=0))]; ext1 i; simp [belly, revolve,sires]
lemma envelope_ext {V U: EnvelopeU D R G r} (hp: ∀ p:Exam D, (plug p R)∘ V=(plug p R)∘ U) : V=U := by
  funext b; ext x; obtain ⟨q,rfl⟩:=doors D R x; exact congr_fun (hp q) b
-- adapter lift to nicer fibers

def moreU (τ p : ℕ)(U:BoardU D R G)(r:ℕ): EnvelopeU D R G r:= if τ ≤ p+r then U (p+r-τ) r else 0
lemma more_tid (hp : Marvel τ U) (p r:ℕ) : Tidy (moreU τ p U r) := by unfold moreU; split; exact hp.hem ..; exact Tidy.zero ..
lemma reel_more {p':ℕ} (φ:Exam D): plug φ R ∘ moreU τ p' U r = Loom.strand τ p' (fun i j=>plug φ R∘ U i j) r := by unfold Loom.strand moreU; split; rfl; exact funext fun _=> map_zero _ -- binder
lemma halo_diff (hu:Marvel τ U)(hp:1/2≤R)(ho:Odd L.val)(hx: Whole X)(hy:Whole Y)(hz:Whole Z)(hf:Speaks X Z Y)(p:Site L)(q:ℕ)(r:ℕ) :
    halo p (moreU τ q U r) Y= halo p (moreU τ q U r) X - ∑ j∈range r,rue p Z (moreU τ q U j) r := by
  let d:=moreU τ q U
  have hm:=halo_tid (w:=p) ho hp (more_tid hu q r) hx; have hn:=halo_tid (w:=p) ho hp (more_tid hu q r) hy
  have ht (j): Tidy (rue p Z (d j) r) := rue_paid ho hp hz (more_tid hu _ _) _
  apply envelope_ext; intro φ; let A:= plug φ R
  rw [show plug φ R∘ (_-_) = _ from (funext fun i=>map_sub .. : (plug φ R∘ (halo p _ X-∑ j∈range r,rue p Z (moreU τ q U j) r)) = (plug φ R∘ halo p (moreU τ q U r) X)-(A∘∑ j∈range r,rue p Z (moreU τ q U j) r)),graft]
  have he i:= Tidy.map A (ht i); have hb: Tidy (∑ j∈range r,A∘rue p Z (d j) r):= Tidy.additions fun i _=>he _
  apply Tidy.uniquely (Tidy.map A hn) ((Tidy.map (plug φ R) hm).less hb); intro m; funext x
  let g:Ratio m (m*L):= ⟨L,rfl⟩; let a : Site m:=0
  have hL:= hf m x
  let P: Exam D:= roll (spinner p) (Carrier.unitStep L) φ
  have hs:= hu.wardrobe (m*L) P (g.assemble (a,p))
  let f:=fun j r=> plug P R ∘ U j r
  have H j k := Tidy.map (plug P R) (hu.hem j k)
  have hz: rootSong ((A∘ halo p (d r) X)-∑ j∈range r,A∘rue p Z (d j) r) m a=rootSong (A∘halo p (d r) X) m a - ∑ j∈range r,rootSong (A∘rue p Z (d j) r) m a := by
    rw [← root_sum a _ (h:=fun i _=> (he i).pens)]; unfold rootSong; rw [st_sub ((Tidy.map A hm).pens.of_norm) hb.pens.of_norm]; rfl
  change rootSong (plug φ R ∘ halo p (d r) Y) m a x=rootSong ((A∘halo p (d r) X)-∑ j∈range r,A∘rue p Z (d j) r) m a x; rw [hz,Pi.sub_apply,Finset.sum_apply]; unfold A d
  rw [halo_pay g a p Y _ (more_tid hu q r) φ hy ho hp,halo_pay g a p X _ (more_tid hu q r) φ hx ho hp] -- need explicit
  simp_rw [fun i=> rue_read (r:=r) g ho hp Z (show Whole Z from ‹Whole Z›) a p φ (more_tid hu q i) x,reel_more]
  obtain ⟨hV,hA⟩:= hf m x; rw [←hV,←hA]; exact lights H hs (installed g Z *ᵥ x) q r

def curse (τ q r h : ℕ)(U:BoardU D R G) (Z:Cross L (Candles G) (Loc G 1)) :=
    ((L.val:ℝ)^h * ((Fintype.card (Site L):ℝ))⁻¹) • ∑ i: Site L,∑ j∈range r,rue i Z (moreU τ q U j) r
lemma abroad (hu:Marvel τ U)(hp:1/2≤R)(ho:Odd L.val)(hx:Whole X)(hy:Whole Y)(hz:Whole Z)(h:Speaks X Z Y)(d e r:ℕ):
    aboard d Y (U e r)=aboard d X (U e r)- if r≤τ+e then curse τ (τ+e-r) r d U Z else 0 := by
  unfold aboard curse; split
  next hg=>
    let q:=τ+e-r; have hh: U e r=moreU τ q U r:=by unfold moreU; rw [if_pos (by unfold q; omega),show q+r-τ=e by unfold q; omega]
    rw [hh]; simp_rw [halo_diff hu hp ho hx hy hz h]; rw [sum_sub_distrib,smul_sub]
  next hg=>
    rw [not_ne_iff.mp (mt (hu.cap e r) hg)]
    have he (K:Cross L (Loc G 1) (Loc G 1))(he:Whole K)(p:Site L): halo p (0:EnvelopeU D R G r) K=0:= by
      ext1 i; unfold Vale.halo belly revolve sires Shade.readdress; simp only [ho,hp,true_and, ↓reduceDIte,Pi.zero_apply]; change (∑' j,_ • (0:Voice _ _))=0; simp
    simp only [fun p=> he X hx p, fun p=> he Y hy p, sub_zero]
end YM.RG08.Needle
