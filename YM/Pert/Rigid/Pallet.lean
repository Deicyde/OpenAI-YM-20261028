import YM.Pert.Position.Detect
import YM.Pert.Rigid.Chess
import YM.UVNext.FREE_STRESS_CERTIFICATE.Cube
/-! Signed-plane action on the actual free curvature label quotient. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option linter.unusedSectionVars false
open scoped Topology Classical BigOperators
namespace YM.Pert.Rigid
open Function UVNext.FreeStress Classical Maxwell Labels Position RawLabels
variable {G : Gauge} (F : Frames G)
abbrev idol := Extra.FD.table_spin F
abbrev wear (d : ℕ) (s : Signed) := (freeTable F).mirror (idol F) d s
abbrev star (c : Option Face) : E F 4:=embed F 4 (sectors c)
def draw (c : Slate) : E F 4 := flat F c.1.1 c.1.2 c.2.1 c.2.2
theorem coincides (c : Face) : star F (some c) = draw F (tape c) := rfl
lemma basis_eq (hg : G.Simple) (c : Option Face) : (stand F hg) c = star F c := by
  rw [stand,Module.Basis.mk_apply];exact rfl

def amplitude (s : Signed) (c : Slate) := (↑(Work.A01.eps s c.1.1 * Work.A01.eps s c.1.2 * (Work.A01.eps s c.2.1 * Work.A01.eps s c.2.2)):ℂ)
theorem draw_turn (s : Signed) (c : Slate) : wear F 4 s (draw F c) = amplitude s c • draw F (mapSlate s.perm c) := signed_link ..
def plain (p : Equiv.Perm Axis) : Signed := ⟨p,fun _ => false⟩
lemma draw_roll (p : Equiv.Perm Axis) (c : Slate) : wear F 4 (plain p) (draw F c) = draw F (mapSlate p c) := by rw [draw_turn]; unfold amplitude Work.A01.eps; rw [show (plain p).perm=p from rfl]; simp [Signed.matrix_at,plain]
lemma ray_twice (s : Signed) (c : Slate) : amplitude s c * amplitude s c = 1 := by unfold amplitude; rw [← Complex.ofReal_mul]; norm_cast; rw [show ∀ a b x d : ℝ, (a*b*(x*d))*(a*b*(x*d))=(a*a)*(b*b)*(x*x)*(d*d) from fun a b x d => by ring]; simp [Work.A01.eps_self]
def badge (a : Axis) (p : Edge) : ℝ := if pop p a then -1 else 1
def flavor (a : Axis) (c : Slate) : ℂ := if paint c a then -1 else 1
lemma badge_frame (a : Axis) (p : Edge) (hp : p.1 ≠ p.2) : Work.A01.eps (Signed.mirror a) p.1 * Work.A01.eps (Signed.mirror a) p.2 = badge a p := by
  simp only [badge,pop,Bool.decide_coe,Work.A01.eps, Signed.matrix_at,if_pos,Signed.mirror]; split_ifs <;> norm_num at * <;> grind
lemma mask_amp (c : Slate) (hc : c.1.1 ≠ c.1.2) (hc' : c.2.1 ≠ c.2.2) (a) : amplitude (Signed.mirror a) c=flavor a c := by
  rw [amplitude, badge_frame _ _ hc, badge_frame _ _ hc']; unfold badge flavor paint; cases pop c.1 a <;> cases pop c.2 a <;> norm_num
lemma map_id (c : Slate) : mapSlate (id:Axis→Axis) c = c := rfl
lemma draw_mask (c : Face) (a) : wear F 4 (Signed.mirror a) (draw F (tape c)) = flavor a (tape c) • draw F (tape c) := by
  rw [draw_turn,mask_amp _ c.val.1.property.ne c.val.2.property.ne]; rfl
lemma flavor_twice (a : Axis) (c : Slate) : flavor a c * flavor a c = 1 := by unfold flavor; split <;> simp
lemma flavor_equal {c d : Slate} (hc : paint c ≠ paint d) : ∃ a, flavor a c ≠ flavor a d := by
  have hz : ∃ a, paint c a ≠ paint d a := by by_contra! ht; exact hc (funext ht)
  obtain ⟨a,h⟩ := hz
  refine ⟨a,?_⟩; unfold flavor; revert h; cases paint c a <;> cases paint d a <;> norm_num

def SameSign (v w : E F 4) := ∃ (a : ℂ), a*a=1 ∧ v=a•w
lemma transSign (v w y : E F 4) (h : SameSign F v w) (hf : SameSign F w y) : SameSign F v y := by
  obtain ⟨a,h,rfl⟩ := h; obtain ⟨c,g,rfl⟩ := hf; exact ⟨a*c,by calc (a*c)*(a*c) = (a*a)*(c*c) := by ring
                                                            _ = 1 := by rw [h,g,mul_one],smul_smul ..⟩
lemma same_at (c d : Slate) (h : same c.1 d.1 ∧ same c.2 d.2) : SameSign F (draw F c) (draw F d) := by
  cases c with
  | mk c1 c2 =>
  obtain ⟨⟨i,k⟩,j,e⟩ := d -- shape?
  change (c1=(i,k) ∨ c1=(i,k).swap) ∧ (c2=(j,e) ∨ c2=(j,e).swap) at h
  rcases h with ⟨h1,h2⟩
  simp only [Prod.swap_prod_mk] at * -- lemma?
  rcases h1 with rfl|rfl <;> rcases h2 with rfl|rfl <;> unfold SameSign draw
  all_goals change ∃ a, _ ∧ _ = _ • link F 4 le_rfl i k j e
  · exact ⟨1,mul_one _,(one_smul ..).symm⟩
  · refine ⟨-1,by simp,?_⟩; rw [neg_smul, one_smul]; exact right_link ..
  · refine ⟨-1,by simp,?_⟩; rw [neg_smul, one_smul]; exact left_link ..
  · refine ⟨1,by simp,?_⟩; rw [one_smul]; change link F 4 le_rfl k i e j = _; rw [right_link _ _ _ _ j e,left_link,neg_neg]
lemma sign_match (c d : Slate) (h : Same c d) : SameSign F (draw F c) (draw F d) := by
  rcases h with h|h;· exact same_at F c d h
  have hc : draw F d.swap = draw F d := swap_link ..
  rw [←hc]; exact same_at F c _ h

def Valid (c : Slate) := c.1.1 ≠ c.1.2 ∧ c.2.1 ≠ c.2.2
lemma refit (c : Slate) (h : Valid c) : ∃ a : Face, Same c (tape a) := by
  have h' (p : Edge) (hp : p.1≠p.2) : ∃ v : Plane, same p v.val := by
    rcases hp.lt_or_gt with w|w; · exact ⟨⟨p,w⟩,Or.inl rfl⟩
    exact ⟨⟨p.swap,w⟩,Or.inr rfl⟩
  obtain ⟨p,hp⟩ := h' c.1 h.1; obtain ⟨q,hq⟩ := h' c.2 h.2
  rcases le_total (keyNo p) (keyNo q) with ht|ht
  · exact ⟨⟨(p,q),ht⟩,Or.inl ⟨hp,hq⟩⟩
  exact ⟨⟨(q,p),ht⟩,Or.inr ⟨hp,hq⟩⟩
lemma valid_tape (p : Face) : Valid (tape p) := ⟨p.val.1.property.ne,p.val.2.property.ne⟩
lemma valid_map (s : Signed) (c : Slate) (h : Valid c) : Valid (mapSlate s.perm c) := ⟨s.perm.injective.ne h.1,s.perm.injective.ne h.2⟩
theorem wearer (s : Signed) (c : Option Face) : ∃ d : Option Face, SameSign F (wear F 4 s (star F c)) (star F d) := by
  cases c with
  | none => exact ⟨none,1,by simp,by change wear F 4 s (embed F 4 (Labels.unit G 4))= 1 • _;rw [one_smul, pin_unit,Table.mirror_unit]; exact (pin_unit F 4).symm⟩
  | some p =>
    rw [coincides,draw_turn]
    obtain ⟨d,h⟩ := refit _ (valid_map s _ (valid_tape p))
    refine ⟨some d,?_⟩; rw [coincides]; exact transSign F _ (draw F (mapSlate s.perm (tape p))) _ ⟨amplitude s (tape p),ray_twice _ _,rfl⟩ (sign_match F _ _ h)
end YM.Pert.Rigid
