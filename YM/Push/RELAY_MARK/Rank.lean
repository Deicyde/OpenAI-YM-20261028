import YM.Push.RELAY_MARK.Ideal
import YM.Push.RELAY_MARK.Powered
import YM.Work.G01
import YM.Work.G02

/-!
# Readable independent family (before symmetrizing)

Crucially not replacing a literal product of forces by a
product of polynomials evaluated on some putative smooth YM field.
When taking combinations matching a continuum symbol at weight `j+2`,
the *other factors can differ* per summand. Choose them disjoint
from that individual varied link, and match them at linear order
simultaneously through **all** higher weights being kept. Keep any
remaining linear tail for the equation leg (need not itself be an
equation polynomial!), obtaining a graph rather than a pure-graded
lift. This gives the rank and supports/population needed by the
source normalization. .
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function Set Filter MeasureTheory Wilson Lattice RG Source Source.Drops Labels Analysis Next.Foundations
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {H : Hol G} {j d n : ℕ}

section Prices

-- small typing lemmas
private lemma funds (c : ℝ) (p : Pulled G d) : spell d (c • p)=(c:ℂ) • spell d p :=
    ((spellMap G d).map_smul c p).trans (IsScalarTower.algebraMap_smul ℂ c (spell d p)).symm
private lemma refund (p q : Pulled G d) : spell d (p+q)=spell d p + spell d q := (spellMap G d).map_add p q
private lemma zero_funds : spell d (0 : Pulled G d)=0 := map_zero (spellMap G d)

lemma safe_observable (H : Hol G) (h : Peg H d) (e : Edge Cover) (p : Pulled G d) :
    ∃ f : Pre G, independent e f ∧ f∈powered G 1 ∧ ∃ q, Forms H d f q ∧ q-spell d p∈floorSlots 2 := by
  have he := safe_span H h e p
  induction he using Submodule.span_induction with
  | mem p hP =>
    obtain ⟨⟨⟨s,hs⟩,i⟩, rfl⟩ := hP
    exact ⟨slotted G s i,(safe_read e s hs (G:=G)).map (fun v : G.Color=> (v i : ℂ)),solo_chip s i,slot_readout H s d i h⟩
  | zero => exact ⟨0,independent.const _,Submodule.zero_mem _,0,Forms.zero ..,by rw [zero_funds]; simp⟩
  | add p q _ _ ih ih' =>
    obtain ⟨f,hf,hv,x,hx,hy⟩ := ih; obtain ⟨g,hg,hG,y,hk,hl⟩ := ih'
    refine ⟨f+g,hf.join hg (·+·), Submodule.add_mem _ hv hG,x+y,hx.add hk,?_⟩
    rw [refund,add_sub_add_comm]; exact Submodule.add_mem _ hy hl
  | smul c p _ ih =>
    obtain ⟨f,hf,hF,x,hx,hy⟩ := ih
    refine ⟨(c:ℂ) • f, hf.map (fun v => (c:ℂ) • v), Submodule.smul_mem _ _ hF,(c:ℂ) • x,hx.scale _,?_⟩
    rw [funds,← smul_sub]; exact Submodule.smul_mem _ _ hy

lemma text_safe (H : Hol G) (h : Peg H d) (e : Edge Cover) (a : List (Ink G))
    (hi : (syntaxRank a).1 ≤ d) :
    ∃ f : Pre G, independent e f ∧ f∈powered G (syntaxRank a).2 ∧ ∃ q, Forms H d f q ∧ q-verse a∈floorSlots ((syntaxRank a).2+1) := by
  induction a with
  | nil =>
    exact ⟨1, independent.const (1:ℂ),base_one _,1,Forms.one ..,by simp [verse]⟩
  | cons i b ih =>
    have hS : syntaxRank (i::b)=badge i+syntaxRank b := by simp [syntaxRank]
    rw [hS] at hi ⊢
    have hB : (syntaxRank b).1 ≤ d := le_trans (Nat.le_add_left ..) hi
    have ht : i.1+2 ≤ d := le_trans (Nat.le_add_right ..) hi
    let x : Fin (d-1) := ⟨i.1,by omega⟩
    obtain ⟨f,hf,hF,p,hp,he⟩ := safe_observable H h e
      (show Pulled G d from i.2.comp (LinearMap.proj (φ:=fun i : Fin (d-1) => Taylor G i.val) x))
    have ht := spell_explicit (d:=d) (j:=x) i.2; erw [ht] at he
    obtain ⟨g,hg,hG,q,hq,hv⟩ := ih hB
    have hw : literal (i.snd)∈sector (badge i) := literal_tier _
    refine ⟨f*g,hf.join hg (·*·),power_prod hF hG,_,hp.product hq,?_⟩
    have hu : verse (i::b) = literal i.2 * verse b := by simp [verse]
    rw [← limited_cap d _ (sector_limited (syntaxRank (i::b)) (hS.symm ▸ hi) (rank_verse _)),hu,← cap_sub]
    exact cap_preserves d (slots_error (slot_sector (badge i) hw) (slot_sector (syntaxRank b) (rank_verse b)) he hv)
end Prices

section Marked

-- Keep actual projection and t-scaling order even when forming const linear combos.
structure Cone (H : Hol G) (d : ℕ) (m : ℕ × ℕ) (p : Pol G) (f : Pre G) (q : Pol G) : Prop where
  grows : p∈sector m
  maps : Forms H d f q
  head : q-p∈above m
  size : f∈powered G m.2
  mark : Micro f

namespace Cone
variable {m : ℕ × ℕ} {f g : Pre G} {p q u v : Pol G}

lemma add (h : Cone H d m p f q) (he : Cone H d m u g v) : Cone H d m (p+u) (f+g) (q+v) :=
    ⟨Submodule.add_mem _ h.grows he.grows,h.maps.add he.maps,by rw [add_sub_add_comm]; exact Submodule.add_mem _ h.head he.head,
      Submodule.add_mem _ h.size he.size,h.mark.add he.mark⟩
lemma scale (c : ℂ) (h : Cone H d m p f q) : Cone H d m (c • p) (c • f) (c • q) :=
    ⟨Submodule.smul_mem _ _ h.grows,h.maps.scale c,by rw [← smul_sub]; exact Submodule.smul_mem _ _ h.head,
      Submodule.smul_mem _ _ h.size,h.mark.scale c⟩
lemma zero (H : Hol G) (d : ℕ) (m : ℕ × ℕ) : Cone H d m 0 0 0 :=
    ⟨Submodule.zero_mem _,Forms.zero ..,by simp,Submodule.zero_mem _, (micros G).zero_mem⟩
end Cone

/-- Assemble at `n` the projection of combos spelling the linearities at d. `p` arbitrary member of the
span even if contaminated with lower weights (so take ALL first-order terms at this assembly). -/
private lemma stanza (H : Hol G) {m : ℕ × ℕ} (x : List (Ink G)) (s : syntaxRank x=m) (h : d ≤ n)
    (hb : m.1 ≤ n) (hd : Peg H d) (hn : Peg H n) (p : Pulled G d) (he : p∈mounted H d) :
    ∃ (f : Pre G) (w : Pol G) (y : Pulled G n), y ∘ₗ wider=p ∧ Forms H n f w ∧
      Micro f ∧ f∈powered G (1+m.2) ∧ w-capRead n (spell n y*verse x)∈floorSlots (1+m.2+1) := by
  induction he using Submodule.span_induction with
  | mem p hP =>
    obtain ⟨⟨b,i⟩,rfl⟩ := hP
    let c := positiveLinear H n b i
    obtain ⟨g,hg,hG,q,hq,hv⟩ := text_safe H hn b.e x (s ▸ hb)
    obtain ⟨u,hu,hU⟩ := force_reads H hn b i
    have hw : verse x∈sector m := s ▸ rank_verse x
    rw [s] at hv hG
    refine ⟨flashed b i*g,_,c,expanded h H b hd hn i,hu.product hq,?_,power_prod (power_force b i) hG,?_⟩
    · convert micro_force ((EuclideanSpace.basisFun G.ColorIndex ℝ) i) g b.w b.e b.open_path (power_cont hG) hg using 1
      funext U; simp only [flashed,Pi.mul_apply,EuclideanSpace.basisFun_inner]
    rw [← cap_sub]
    exact cap_preserves n (slots_error (spell_slot _) (slot_sector m hw) hU hv)
  | zero => refine ⟨0,0,0,?_,Forms.zero ..,(micros G).zero_mem,Submodule.zero_mem _,?_⟩
            · simp
            rw [zero_funds]; simp [cap_is]
  | add p q _ _ ih ih' =>
    obtain ⟨f,u,a,hp,hF,hf,hv,ha⟩ := ih; obtain ⟨g,v,b,hq,hG,hg,hz,hb⟩ := ih'
    refine ⟨f+g,u+v,a+b,by rw [LinearMap.add_comp,hp,hq],hF.add hG,hf.add hg,Submodule.add_mem _ hv hz,?_⟩
    rw [refund,add_mul,cap_is,map_add,← cap_is,← cap_is,add_sub_add_comm]; exact Submodule.add_mem _ ha hb
  | smul c p _ ih=>
    obtain ⟨f,u,a,hp,hF,hf,hv,ha⟩ := ih
    refine ⟨(c:ℂ) • f,(c:ℂ) • u,c • a,by rw [LinearMap.smul_comp,hp],hF.scale _,hf.scale _,Submodule.smul_mem _ _ hv,?_⟩
    rw [funds,smul_mul_assoc,cap_is,map_smul, ← cap_is,← smul_sub]; exact Submodule.smul_mem _ _ ha

lemma coherent_verse (H : Hol G) (hp : ∀ k, Peg H k) (x : Ink G) (hx : Gap x) (a : List (Ink G))
    (hb : (badge x+syntaxRank a).1 ≤ d) :
    ∃ f q,Cone H d (badge x+syntaxRank a) (literal x.2*verse a) f q := by
  let k := x.1+2
  have hk : k ≤ d := le_trans (Nat.le_add_right ..) hb
  let T : Fin (k-1) := ⟨x.1,by unfold k; omega⟩
  let p : Pulled G k := x.2 ∘ₗ (LinearMap.proj (φ:=fun i : Fin (k-1) => Taylor G i.val) T)
  let m := badge x+syntaxRank a
  have hw : literal x.2*verse a∈sector m := sector_mul (literal_tier x.2) (rank_verse _)
  obtain ⟨f,w,y,hp',hF,hf,hW,hl⟩ := stanza H a rfl hk (le_trans (Nat.le_add_left ..) hb) (hp _) (hp _) p
    (force_span H (hp _) x.2 hx)
  refine ⟨f,w,hw,hF,?_,hW,hf⟩
  have hY := higher_linear hk y
  rw [hp', show spell k p=literal x.2 from spell_explicit (d:=k) (j:=T) _] at hY
  let z := spell d y*verse a
  let v := literal x.2*verse a
  have hh : z-v∈above m := by
    unfold z v; rw [← sub_mul,mul_comm _ (verse _)]
    unfold m; rw [add_comm]; apply rising_mul (m:=syntaxRank a) (n:=badge x) (rise_sector (syntaxRank a) (rank_verse a)) hY
  have h' : capRead d z-v∈above m := by
    have he := cap_preserves d hh
    simpa only [above,cap_sub,limited_cap d v (sector_limited m hb hw)] using he
  have ht : w-capRead d z ∈ above m := rise_later (bySlots (b:=(0,1+(syntaxRank a).2+1)) (Nat.lt_add_one m.2)) hl
  change w-v∈_
  rw [← sub_add_sub_cancel w (capRead d z) v]; exact Submodule.add_mem _ ht h'

/-- Unconditional projection-rank producer at relation `Cone`: one raw lift per *any*
member of the actual equation ideal, at pure grade. -/
theorem mounted_read (H : Hol G) (p : Label G d) (m : ℕ × ℕ) (h : m.1 ≤ d)
    (hp : p∈Grade m) (hv : p∈Maxwell.equationIdeal G d) :
    ∃ f q,Cone H d m p.val f q := by
  have he := generation_ready p hv m hp
  have fg (k) : Peg H k := Work.G02.answer Work.G01.answer G H k
  refine Submodule.span_induction (p:=fun v _=> ∃ f q,Cone H d m v f q) ?_ ?_ ?_ ?_ he
  · rintro _ ⟨x,hX,b,hb,rfl⟩; rw [hb] at h ⊢; exact coherent_verse H fg x hX b h
  · exact ⟨0,0,Cone.zero ..⟩
  · rintro x u _ _ ⟨f,q,hf⟩ ⟨g,y,hg⟩; exact ⟨_,_,hf.add hg⟩
  rintro c x _ ⟨f,q,hf⟩; exact ⟨_,_,hf.scale c⟩
end Marked
end YM.Push.Mark
