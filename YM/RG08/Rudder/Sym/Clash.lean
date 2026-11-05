import YM.RG08.Rudder.Sym.Survey

noncomputable section
namespace YM.RG08.Rudder.Symmetry
open scoped Topology BigOperators Classical ENNReal
open Forms Packets Finset Function Lattice Pert.Bulk Exterior Laurent AnalyticNext.QuarticMatch.BoxChain
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I:Type}{n:ℕ}{j l:Fin n}{F:Raw I n}

def field (F:Raw I n)(i:Fin n)(b:ℕ):Prop:=∀ x:Tape n (Market (Tone I)),(x i).2.1.card≠b→F x=0
lemma graded_iff {r:Fin n→ℕ}: Graded F r ↔ ∀ k,field F k (r k):=⟨fun h _ _ hh=>graded_at h hh,fun h y i x hh=>h i (lyre x y) hh⟩
lemma rank_iff (F:Raw I n)(r)(j):field F j r↔∀ y,Rank (hum F y) j r:=⟨fun h y i hi=> h (lyre i y) hi,fun h x hx=>h (fun j=>(x j).2.2) (fun j=>((x j).1,(x j).2.1)) hx⟩
lemma passive {r:ℕ}(h:field F l r)(he:l≠j):field (boundary j F) l r:=by
 rw [rank_iff] at h ⊢;intro y; exact (h y).keeps he
lemma enters {r:ℕ}(h:field F j (r+1)):field (boundary j F) j r:=by rw [rank_iff] at h ⊢;intro y; exact (h y).descent
lemma inactive (u:Tablet)(r:ℕ)(s:Signed): ((marks s u).card=r)=(u.card=r):=by rw [marked_card]
lemma field_orbit (s:Signed){r:ℕ}(h:field F j r):field (orbit s F) j r:=by intro x hx;rw [orbit_apply,h _ (show (marks s _).card≠_ by rw [marked_card];exact hx),mul_zero]

def kick (x:Market (Tone I))(a:Axis)(v:Cover): Market (Tone I):=(x.1+v,insert a x.2.1,x.2.2)
def lifted (a:Axis)(j:Fin n)(F:Raw I n)(x:Tape n (Market (Tone I))):ℝ:= if a∈(x j).2.1 then 0 else
 sign (x j).2.1 a * (F (update x j (kick (x j) a (-step a))) - F (update x j (kick (x j) a 0)))
lemma chart (F:Raw I n)(j)(x): boundary j F x=∑ a,lifted a j F x:=by
 let y(k:Fin n):=((x k).1,(x k).2.1); let z(k:Fin n):=(x k).2.2
 have he (a:Axis)(v:Cover) : lyre (update y j ((x j).1+v,insert a (x j).2.1)) z = update x j (kick (x j) a v):=by
    funext k;by_cases hk:k=j <;>simp [hk,kick,lyre,y,z]
 change lower j (hum F z) y= _;rw [lower_at];apply sum_congr rfl;intro i _
 unfold lifted;rw [sect_at];change (if i∈(x j).2.1 then _ else _) = _;split_ifs;rfl
 unfold peek hum;change sign _ i*(F _-F _)=_
 rw [←he,←he,add_zero]; congr 2 -- minus add

lemma invariantMark (x:Tape n (Market (Tone I)))(s:Signed)(y:Market (Tone I)) : markTape s (update x j y)=update (markTape s x) j (markCell s y):=by rw [markTape_apply,comp_update, markTape_apply]

private lemma short (T:Tablet)(s:Signed)(i:Axis)(h:i∉T):marks s (insert i T)=insert (s.perm i) (marks s T) ∧ evil s (insert i T)=stub s i+evil s T :=⟨image_insert ..,sum_insert h⟩

/- positions for a new incident slot -/
lemma kicked (x:Market (Tone I))(s:Signed)(a:Axis)(ha:a∉x.2.1):
 (markCell s (kick x a 0)=kick (markCell s x) (s.perm a) (if s.flip a=true then -step (s.perm a) else 0))∧
 (markCell s (kick x a (-step a))=kick (markCell s x) (s.perm a) (if s.flip a=true then 0 else -step (s.perm a))):=by
 obtain ⟨h,H⟩:=short x.2.1 s a ha
 cases hh:s.flip a <;> simp [kick,markCell,Signed.act_neg,Signed.act_add,slot,hh,h,H,stub,add_comm,add_left_comm, add_assoc]
-- slot private from Survey need public

def rest (s:Signed)(x:Tape n (Market (Tone I)))(j:Fin n):=∏ k∈univ.erase j,toll s (x k).2.1
lemma levy_advance(s:Signed)(x:Tape n (Market (Tone I)))(w:Market (Tone I)):
 levy s (update x j w)=toll s w.2.1*rest s x j:=by rw [levy,← Finset.mul_prod_erase _ _ (mem_univ j),update_self,rest];congr 1; apply prod_congr rfl; intro i hi;rw [update_of_ne (mem_erase.mp hi).1]
lemma rest_self(s:Signed)(x:Tape n (Market (Tone I)))(j:Fin n):levy s x=toll s (x j).2.1*rest s x j:=by conv_lhs=> rw [←update_eq_self j x];rw [levy_advance] -- check name

lemma usage (F:Raw I n)(s:Signed)(x:Tape n (Market (Tone I)))(i a:Axis)(hx:(x j).2.1={i}) :
     lifted a j (orbit s F) x = levy s x * lifted (s.perm a) j F (markTape s x):=by
 have he:(markTape s x j).2.1= marks s {i}:=congr_arg (marks s) hx
 by_cases hi:a=i
 · subst a;unfold lifted;rw [hx,if_pos (mem_singleton_self _),he,if_pos ((marked ..).mpr (mem_singleton_self _)),mul_zero]
 have hh:a∉({i}:Tablet):=by simpa
 unfold lifted;rw [hx,if_neg hh,he,if_neg (fun h=>hh ((marked ..).mp h)),marks,Finset.image_singleton]
 simp_rw [orbit_apply,invariantMark,levy_advance,rest_self s x j,hx]
 have hz:=toll_next s hi
 have hy:=kicked (x j) s a (by rwa [hx])
 rw [hy.1,hy.2]
 change sign {i} a*( toll s (insert a (x j).2.1)*_*_ - toll s (insert a (x j).2.1)*_*_) = _
 rw [hx]
 unfold spin at hz
 rw [←show markCell s (x j)=markTape s x j from rfl] -- wrong orientation? rw ← gives tape->cell
 cases hf:s.flip a <;> simp only [hf,Bool.false_eq_true,if_false,if_true,mul_one,mul_neg] at hz ⊢
 · rw [show ∀ (t u r v w:ℝ), t*(u*r*v-u*r*w)=t*u*r*(v-w) by intros;ring,←hz]; ring -- goals inspect
 · rw [show ∀ (t u r v w:ℝ), t*(u*r*v-u*r*w)=t*u*r*(v-w) by intros;ring,←hz];ring

lemma commute (F:Raw I n)(s:Signed)(j:Fin n)(h:field F j 2): boundary j (orbit s F)=orbit s (boundary j F):=by
 ext x; by_cases he:(x j).2.1.card=1
 · rw [orbit_apply,chart,chart,Finset.mul_sum, ←Equiv.sum_comp s.perm (fun k=> levy s x*lifted k j F (markTape s x))]
   obtain ⟨a,ha⟩:=Finset.card_eq_one.mp he;exact sum_congr rfl fun i _=>usage F s x a i ha
 · rw [enters (r:=1) (field_orbit s h) x he,field_orbit s (enters (r:=1) h) x he]
end YM.RG08.Rudder.Symmetry
