import YM.RG08.Carrel.Wing

/-!
# Symmetries on finite periodizations: compressed initial corner shift.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Carrel
open Lattice Laurent Forms Pert.Bulk Isles Packets Rudder Rudder.Symmetry Filter Finset Function RG Extra.Iteration
open Exterior
open scoped BigOperators Topology Classical ENNReal
variable {I:Type}{k n:ℕ}{P:Side}
-- compression is at all headline types.
abbrev Firm (I:Type)(k:ℕ) := Anchor.Kind I k
abbrev Cmix (P:Side)(I:Type)(k:ℕ):=Cove P (Firm I k)
abbrev Mix (I:Type)(k:ℕ):=Market (Firm I k)

def cash (s:Signed)(x:Firm I k):Firm I k:=(⟨marks s x.1.val,(marked_card s ..).trans x.1.property⟩,x.2)
def old (x:Firm I k): Tone I:=(x.1.val,x.2)
def supply (s:Signed)(x:Firm I k):=toll s x.1.val

def atlas (s:Signed)(x:Mix I k):Mix I k:=((markCell s (x.1,old x.2)).1,cash s x.2)
def badge (s:Signed)(x:Cmix P I k):Cmix P I k:=(s.act x.1+wrap P (evil s x.2.1.val),cash s x.2)

lemma atlas_com (s t:Signed)(x:Mix I k):atlas s (atlas t x)=atlas (s*t) x:=by
 apply Anchor.ec_injective; exact markCell_double s t (x.1,old x.2)
lemma atlas_id (x:Mix I k):atlas 1 x=x:=by apply Anchor.ec_injective;exact markCell_one ..
lemma badge_atlas (x:Mix I k)(s:Signed):badge s (port P x)=port P (atlas s x):=by
 unfold badge port atlas markCell;dsimp;rw [wrap_signed,map_add];rfl
lemma badge_com (s t:Signed)(x:Cmix P I k):badge s (badge t x)=badge (s*t) x:=by
 rw [←(show port P (reach x)=x from Prod.ext (wrap_lift x.1) rfl),badge_atlas,badge_atlas,badge_atlas,atlas_com]
lemma badge_id(x:Cmix P I k):badge 1 x=x:=by rw [←(show port P (reach x)=x from Prod.ext (wrap_lift x.1) rfl),badge_atlas,atlas_id]
def citadel (s:Signed):Equiv.Perm (Cmix P I k):=⟨badge s,badge s⁻¹,fun _=>by rw [badge_com,inv_mul_cancel,badge_id],fun _=>by rw [badge_com,mul_inv_cancel,badge_id]⟩
def lodge (s:Signed):Equiv.Perm (Mix I k):=⟨atlas s,atlas s⁻¹,fun _=>by rw [atlas_com,inv_mul_cancel,atlas_id],fun _=>by rw [atlas_com,mul_inv_cancel,atlas_id]⟩
lemma housing(s t:Signed)(x:Firm I k):supply (s*t) x=supply t x * supply s (cash t x):=toll_double ..
lemma stand(s:Signed)(x:Firm I k):|supply s x|=1:=toll_normal ..
lemma stand_slide(s:Signed)(x:Slide (Firm I k) n): |∏ i,supply s (x i).2|=1:=by simp only [Finset.abs_prod,stand,prod_const_one]

def adjust(s:Signed)(F:Flake n (Mix I k)):Flake n (Mix I k):=fun x=> (∏ i,supply s (x i).2)*F (atlas s ∘ x)
lemma adjust_compress (s:Signed)(F:Raw I n): adjust s (Anchor.compress k F)=Anchor.compress k (orbit s F):=rfl
lemma adjustment (s:Signed)(x:Mix I k)(u:Cover):atlas s (pass u x)=pass (s.act u) (atlas s x):=by
 unfold atlas markCell pass;rw [Signed.act_add];ext1
 · exact add_right_comm _ _ _
 rfl

lemma adjust_cohort {F:Flake n (Mix I k)}(h:Cohort F)(s:Signed):Cohort (adjust s F):=by
 intro u x
 unfold adjust; rw [show atlas s ∘ sway u x=sway (s.act u) (atlas s ∘ x) from funext (fun i=> adjustment s (x i) u),h];rfl
lemma adjust_cost {F:Flake n (Mix I k)}{σ p:ℝ}(h:Held (carpet _) σ p F)(hs:0≤σ)(s:Signed):Held (carpet _) σ (p*Real.exp (8*σ)) (adjust s F):=by
 rw [show adjust s F=Anchor.compress k (orbit s (Anchor.extend k F)) from ?_]
 · exact Anchor.compress_cost _ (orbit_held (Anchor.expand_cost h) hs _)
 rw [←adjust_compress];congr 1;ext z;exact (Anchor.extend_top F z).symm

-- period equivalence via free origin from lantern (or neck+grown).
private def bedazzle (s:Signed)(i:Fin n)(z:Tape n (Cmix P I k)):= (reach (badge s (z i))).1 -(atlas s (reach (z i))).1
private def tossed (s:Signed)(i:Fin n)(z:Tape n (Cmix P I k))(x:Tape n (Mix I k)):=sway (bedazzle s i z) (atlas s ∘ x)
private lemma zeroBed (s:Signed)(i:Fin n)(z:Tape n (Cmix P I k)):wrap P (bedazzle s i z)=0:=by
 rw [bedazzle,map_sub,reach,wrap_lift]
 have he:=congrArg Prod.fst (badge_atlas (P:=P) (reach (z i)) s)
 rw [show port P (reach (z i))=z i from Prod.ext (wrap_lift _) rfl] at he
 exact sub_eq_zero.mpr he
private lemma landToss{s:Signed}{i:Fin n}{z:Tape n (Cmix P I k)}{x:Slide (Firm I k) n}(h:x∈lantern i z):tossed s i z x∈lantern i (badge s ∘ z):=by
 constructor
 · have he:x i=reach (z i):=h.1
   unfold tossed sway pass bedazzle;dsimp only [comp_apply];rw [he]; ext1
   · dsimp;abel
   rfl
 funext j
 have hh:=found h j
 change port P (pass (bedazzle s i z) (atlas s (x j))) = badge _ _
 rw [←hh,badge_atlas];apply Prod.ext
 · unfold port pass;dsimp;rw [map_add,zeroBed,add_zero]
 rfl
private lemma gone (s:Signed)(i:Fin n)(z:Tape n (Cmix P I k)) (x:Slide (Firm I k) n):tossed s⁻¹ i (badge s ∘ z) (tossed s i z x)=x:=by
 have he(k:Mix I k):atlas s⁻¹ (atlas s k)=k:=(lodge s).left_inv k
 have hm : s⁻¹.act (bedazzle s i z)+bedazzle s⁻¹ i (badge s ∘ z)=0:=by -- neg precedence
    let d:= reach (z i)
    have hx: atlas s d = pass (-(bedazzle s i z)) (reach (badge s (z i))):=by
      apply Prod.ext;change _ = _+-(_-_);abel
      rfl
    have hh:=he d; rw [hx,adjustment] at hh
    have ht:= congrArg Prod.fst hh
    change _+ (s⁻¹).act (- (bedazzle s i z))=d.1 at ht
    unfold bedazzle;dsimp only [comp_apply];rw [badge_com,inv_mul_cancel,badge_id] -- defeq badge badge
    rw [Signed.act_neg] at ht
    change _+(d.1-_)=_;rw [←ht];unfold bedazzle;abel
 funext j;unfold tossed sway;dsimp only [comp_apply];rw [adjustment,he,pass_pass,add_comm,hm,pass_zero]

def swapbed (s:Signed)(i:Fin n)(z:Tape n (Cmix P I k)):lantern i z≃lantern i (badge s ∘ z) :=by
 -- dependent cast trick inv: land then using badge^-1(badge z) =z; right inverse use eq_subst
 have ha(s:Signed)(z:Tape n (Cmix P I k)): badge s⁻¹ ∘ (badge s ∘ z)=z:=funext fun j=>(citadel s).left_inv (z j)
 let back (x:Tape n (Mix I k)):=tossed s⁻¹ i (badge s ∘ z) x
 refine ⟨fun x=>⟨_,landToss x.property⟩,fun x=>⟨back x.val,(show back x.val∈lantern i z by have H:=landToss (s:=s⁻¹) x.property; have ht :back x.val∈lantern i (badge s⁻¹ ∘ (badge s ∘ z)):= H; simpa [ha s z] using ht)⟩,fun x=>Subtype.ext (gone s i z x.val),?_⟩
 intro x
 apply Subtype.ext;change tossed s i z (tossed s⁻¹ i (badge s ∘ z) x.val)= x.val
 nth_rw 1 [← ha s z,←inv_inv s];rw [gone]

lemma toured {s:Signed}{F:Flake n (Mix I k)}(H:Cohort F)(i:Fin n)(z:Tape n (Cmix P I k)):
 pour (adjust s F) i z =(∏ i,supply s (z i).2)*pour F i (badge s ∘ z):=by
 rw [pour_at,pour_at,←(swapbed s i z).tsum_eq,←tsum_mul_left];apply tsum_congr;intro x
 change adjust s F x.val=_*F (tossed _ _ _ _)
 rw [tossed,H]; apply congrArg₂ (·*·) _ rfl;apply Finset.prod_congr rfl;intro j _;rw [show (x.val j).2=(z j).2 from congrArg (fun w:Cmix P I k =>w.2) (found x.property j)]
end YM.RG08.Carrel
