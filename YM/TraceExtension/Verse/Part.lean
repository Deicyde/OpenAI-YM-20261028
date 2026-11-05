import YM.TraceExtension.Verse.Curtain
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Verse
open Function Filter Set Extraction Cells OS OS.Ground Lattice Spec MeasureTheory Table Word
open scoped Topology BigOperators InnerProductSpace
variable {G: Gauge} {C: Family G} {F: Filter (ℕ×ℕ)} {f:Extraction.Order} {S:Table C.book} {V:Chamber S timeAxis}{A:Spread V} {p:A.Resolution}{k b n d: ℕ}
-- specialize this film and use singleton/pair
structure Duo (C:Family G)(F:Filter (ℕ×ℕ))(k d : ℕ) where
    y : Fin 2→Cover
    gen : Extraction.Order.grid C k y ∈ generic 2
    reading (i:Fin 2)(t:ℕ×ℕ): C.label d
    real (i:Fin 2): C.label d
    goal (i:Fin 2): Tendsto (reading i) F (𝓝 (real i))

namespace Duo
variable (B:Duo C F k d)(Z : Fin 2→ℂ)(z:ℂ)
private structure Monomial where
  coeff : ℂ
  arity : ℕ
  slot : Fin arity → Fin 2
  separate : Injective slot
private def blank (x:ℂ):Monomial:=⟨x,0,Fin.elim0,fun _ _ _=>Subsingleton.elim ..⟩
private def unary (x:ℂ)(j:Fin 2):Monomial:=⟨x,1,fun _=>j,fun _ _ _=>Subsingleton.elim ..⟩
private def pair (x:ℂ):Monomial:=⟨x,2,id,Function.injective_id⟩
private def enact (q:Fin n→Monomial):Scene C F k where
  num:= n
  factor i:= (q i).coeff
  image i:= (q i).arity
  seats i j:= B.y ((q i).slot j)
  gen i a:= (B.gen a).comp (q i).separate
  weight _ _:= d
  point i j:= B.real ((q i).slot j)
  current i j N p:= B.reading ((q i).slot j) (N,p)
  views _ _:= B.goal _

def shoots (N p:ℕ)(i:Fin 2):= C.O N p (B.reading i (N,p)) (location C.S k N p (B.y i))
def cut1 (i:Fin 2)(N p:ℕ)(u:Wilson.Config G (C.side N p)):= B.shoots N p i u-Z i
def cut2 (N p:ℕ)(u:Wilson.Config G (C.side N p)):= cut1 B Z 0 N p u * cut1 B Z 1 N p u-z
-- root payments before limits
set_option quotPrecheck false
-- open Wilson
structure Buys (b:ℕ)(c:ℝ):Prop where
    pos:c≥0
    wide:b≤k
    buys: ∀ᶠ i:ℕ×ℕ in F, ∃ hk:k ≤ i.1,
      let T:= Cells.center C.S i.2 (wide.trans hk) 0
      (∀ x: Fin 2, Interior (T.chamber 0) (B.shoots i.1 i.2 x) ∧ T.rootTest (C.beta i.1 i.2) (cut1 B Z x i.1 i.2) ≤ c) ∧ T.rootTest (C.beta i.1 i.2) (cut2 B Z z i.1 i.2) ≤ c

def twig (i : Fin 2):C.book.Plant:=((Extraction.Order.grid C k B.y) i,⟨d,B.real i⟩)
lemma receipt [F.NeBot] (Y:Seed C f S)(hf:F ≤ f.fuse)(H:p.Out)(hv:Steady V){x:p.X→Table C.book}(hs:∀ i,(x i).Hierarchy)(hq:∀ i,p.receives (x i) i)(x':p.X){c:ℝ}(he:Buys B Z z b c):
    ‖(x x').read (Extraction.Order.grid C k B.y) (fun j=>⟨d,B.real j⟩)-(Z 0*Z 1+z)‖ ≤ c+(‖Z 0‖+‖Z 1‖)*c:=by
    let S':=(x x'); let U:=S'.expect
    have h₀:U []=1:= (hs x').laws.trivial ..
    have hh(q: Scene C F k):p.character x' (q.cluster A)=∑ i,q.factor i * U (q.word i):=by simp [Scene.cluster,Retain.pops A p (hq x'),U,S']
    have hu(N p)(hb':b≤N)(i:Fin 2)(hy:Interior ((Cells.center C.S p hb' 0).chamber 0) (B.shoots N p i)):Interior ((Cells.center C.S p hb' 0).chamber 0) (cut1 B Z i N p):=by
       unfold cut1; simpa only [sub_eq_add_neg] using hy.plus (Interior.constant _ (- Z i))
    have hg(i:Fin 2): ‖U [B.twig i]-Z i‖≤c:=by
       let q:= B.enact ![unary 1 i, blank (-Z i)]
       have hx N p:q.cuts N p 0=cut1 B Z i N p:=by
          funext u; simp only [q,Scene.cuts,enact,add_zero]; change 1*(B.shoots N p i u*1)+((-Z i)*1+0)=_;simp [cut1,sub_eq_add_neg]
       have hb:= ticket Y hf H hv hs hq c he.pos he.wide q (by
          filter_upwards[he.buys] with t ht; obtain ⟨hk,hk',-⟩:=ht; exact ⟨hk,(hx _ _).symm ▸ hu t.1 t.2 (he.wide.trans hk) i (hk' i).1,(hx _ _).symm ▸ (hk' i).2⟩) x'
       rw [hh] at hb
       change ‖1*U [B.twig i]+((-Z i)*U []+0)‖ ≤ _ at hb; simpa [h₀, sub_eq_add_neg] using hb
    let r:= B.enact ![pair 1, unary (-(Z 0)) 1, unary (-(Z 1)) 0,blank (Z 0*Z 1-z)]
    have hi N p:r.cuts N p 0=cut2 B Z z N p:=by
        funext u; simp only [r,Scene.cuts,enact,add_zero,cut2,cut1]; change 1*(B.shoots N p 0 u*(B.shoots N p 1 u*1))+ ((-Z 0)*(B.shoots N p 1 u*1)+((-Z 1)*(B.shoots N p 0 u*1)+((Z 0*Z 1-z)*1+0)))=_; ring
    have hc:= ticket Y hf H hv hs hq c he.pos he.wide r (by
       filter_upwards [he.buys] with t ht; obtain ⟨hk,hk',hY⟩:= ht
       refine ⟨hk,?_,(hi _ _).symm ▸ hY⟩
       rw [hi]; unfold cut2; simpa only [sub_eq_add_neg] using
           ((hu t.1 t.2 (he.wide.trans hk) 0 (hk' 0).1).times (hu t.1 t.2 (he.wide.trans hk) 1 (hk' 1).1)).plus (Interior.constant _ (- z))) x'
    rw [hh] at hc
    let a:= Z 0;let e:=Z 1;let i0:=U [B.twig 0];let i1:=U [B.twig 1]; let X:= S'.read (Extraction.Order.grid C k B.y) (fun j=>⟨d,B.real j⟩)
    change ‖1*U (r.word (0:Fin 4))+(-(Z 0)*i1+(-(Z 1)*i0+((a*e-z)*U []+0)))‖ ≤ c at hc
    let Δ:= X-(a*i1+e*i0)+(a*e-z)
    have hz: ‖Δ‖ ≤ c:=by
      rw [show U (r.word (0:Fin 4))=X from by exact S'.readAt (fun j=>⟨d,B.real j⟩) _] at hc
      rw [h₀] at hc; refine le_trans ?_ hc; apply le_of_eq; congr 1; change X-(a*i1+e*i0)+(a*e-z)= 1*X+(-a*i1+(-e*i0+ ((a*e-z)*1+0))); ring
    change ‖X-(a*e+z)‖≤ _
    rw [show X-(a*e+z)= Δ+(a*(i1-e)+e*(i0-a)) from by unfold Δ;ring,add_mul]
    refine (norm_add_le ..).trans (add_le_add hz ((norm_add_le ..).trans ?_)); rw [norm_mul,norm_mul]; exact add_le_add (mul_le_mul_of_nonneg_left (hg _) (norm_nonneg _)) (mul_le_mul_of_nonneg_left (hg _) (norm_nonneg _))
end Duo
end YM.Trace.Verse
