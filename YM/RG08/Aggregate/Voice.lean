import YM.RG08.Aggregate.Fam

/-!
# Exact symbol Ward at INPUT of supported gauge-invariant packets and completions,
 also infinite deck. Includes rescaled g-gauges by adjoining gauge parameters as fields.
 Does not assert at after-heating or on quotient. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Aggregate
open Carrel Camera Room Cloud Glyph Lattice Laurent Function Finset Filter
open RG Wilson Forms Isles Pert.Bulk Rudder Symmetry Anchor MvPolynomial
open scoped BigOperators Topology ENNReal PowerSeries Classical ContDiff
variable {I:Type}[Fintype I]{G:YM.Gauge}{n k:ℕ}{P:Side}
variable {F:Rudder.Raw G.ColorIndex n}{σ p:ℝ}

lemma reserve (i:Fin n)(v:Fin k)(_h:Cohort F)(he:Held (carpet _) σ p F)(hp:0≤p)(hs:0<σ):
 tap k (booked F i P)=parley (pour (P:=P) (completed F i k) v):=by
 obtain ⟨D,hD,H⟩:=completed_held G k i hs
 unfold tap booked; rw [PowerSeries.coeff_mk,component,dif_pos v.pos];congr 1;ext1 z; exact common (H F hp he).2.2 _ v _
lemma booked_low (P:Side)(i:Fin n)(h:Cohort F)(he:Held (carpet _) σ p F)(hp:0≤p)(hs:0<σ):Low n (booked F i P):=by
 intro k hk;by_cases hq:0<k
 · let v:Fin k:=⟨0,hq⟩;rw [reserve i v h he hp hs, early_vanish i h he hp hs v hk]; unfold pour; simp [Set.indicator];exact parley_zero -- inspect
 rw [show k=0 by omega,tap,booked,PowerSeries.coeff_mk,component,dif_neg (Nat.lt_irrefl _)];

lemma annPull (A:Camera.Strip (Bedge G P) I)(hA:∀ i, Camera.Pace (A i))(h0:Camera.roll A 0=0)(i:Fin n)(b:Coord (n:=n)):
 belt (rescaleFields A) (annulus F i P b)=(Fintype.card Signed:ℝ)⁻¹ • ∑ s:Signed,∑ o:Site P, flask (atoms F i b s o ∘ Camera.roll A):=by
 simp_rw [annulus,_root_.map_smul,map_sum, flask_comp hA h0 (atom_pace ..)]

/-- Given exact path gauge equivariance on slices/symmetries at real unreduced coordinates, outputs
 FPS equality in centered symbols. Does not pass to limits in the laws themselves. Operators
 must keep every constituent in same pressure phase & sign; here signed/translation permutation
 i→a(i), field gauge may depend on signature & value (true local site gauges). -/
lemma subtended (A B:Camera.Strip (Bedge G P) I)(hA:∀ j, Camera.Pace (A j))(hB:∀ j,Camera.Pace (B j))(he:Camera.roll A 0=0)(hN:Camera.roll B 0=0)(m:Equiv.Perm (Signed × Site P))
   (i:Fin n)(h:Cohort F)(hν:hue (dressed G n) F)(hs:0<σ)(hp:0≤p)(hC: Held (carpet _) σ p F)
   (hu:∀ (s:Signed × Site P),∀ᶠ x:Cellar I in 𝓝 0, ∃ t:Cover→G.El, expandAt (m s).2 (Lattice.pull (m s).1 0 (offers G (Camera.roll B x)))=
     Lattice.gauge t (expandAt s.2 (Lattice.pull s.1 0 (offers G (Camera.roll A x))))):
    belt (rescaleFields A) (booked F i P)=belt (rescaleFields B) (booked F i P):=by
 have heq(x : Coord (n:=n))(s:Signed × Site P):(atoms F i x s.1 s.2 ∘ Camera.roll A)=ᶠ[𝓝 0](atoms F i x (m s).1 (m s).2 ∘ Camera.roll B):=by
    filter_upwards [hu s] with z hz
    obtain ⟨t,hz⟩:=hz
    let a:=deposit (compress 2 F) i x
    have hb(y:Cellar (Bedge G P))(q:Signed)(v:Site P):showAtom a v (Crown.turns q y)=a.poly (fun j=> (a.leg j).eval (expandAt v (Lattice.pull q 0 (offers G y)))):=by rw [Crown.turns_affine]; unfold showAtom;rw [tread];rfl -- use tread
    change showAtom a _ (Crown.turns _ (Camera.roll _ z))=showAtom a _ (Crown.turns _ (Camera.roll _ z))
    rw [hb,hb,hz];simp_rw [Work.F05.slot_cover_gauge];symm; exact lit _ (compressed _ hν) i x _ _
  -- after pulling each path and changing aggregate no need reindex path b. only origin/sign.
 have hx(b:Coord (n:=n)): belt (rescaleFields A) (annulus F i P b)=belt (rescaleFields B) (annulus F i P b):=by
    rw [annPull _ hA he,annPull _ hB hN];apply congrArg (fun x:Port I=>(Fintype.card Signed:ℝ)⁻¹ • x)
    rw [←Fintype.sum_prod_type (fun u:Signed×Site P=> flask (atoms F i b u.1 u.2 ∘ Camera.roll A)),←Fintype.sum_prod_type (fun u:Signed×Site P=> flask (atoms F i b u.1 u.2 ∘ Camera.roll B))]
    conv_rhs=>rw [←Equiv.sum_comp m]
    apply Finset.sum_congr rfl;intro r _;exact flask_same (heq b r)
 ext k :1;apply MvPolynomial.funext;intro x
 have hw:=driven h hC hp hs i k (rescaleFields A) x;have hg:=driven h hC hp hs i k (rescaleFields B) x
 simp_rw [hx] at hw
 exact hw.unique hg

def reposition (s:Signed)(v:Site P):Equiv.Perm (Signed×Site P):=by
 let f (x:Signed×Site P):= x.2 - ((s⁻¹*x.1)⁻¹).act (s⁻¹.act v) -- check below
 let g (x:Signed×Site P):=x.2 + x.1⁻¹.act (s⁻¹.act v)
 refine ⟨fun x=>(s⁻¹*x.1,f x),fun x=>(s*x.1,g x),?_,?_⟩
 · rintro ⟨x,h⟩;simp [f,g]
 rintro ⟨x,h⟩;simp [f,g]

lemma rewrites (s:Signed)(v:Site P)(V : Config G P)(t:Site P→G.El)(i : Signed×Site P): let m:=reposition s v
     ; ∃ t':Cover→G.El, expandAt (m i).2 (Lattice.pull (m i).1 0 (Lattice.gauge t (Lattice.pull s v V)))=
        Lattice.gauge t' (expandAt i.2 (Lattice.pull i.1 0 V)):=by
 -- compose gauge pull matrix: after pull s v, pull y=s^-1*i, pull_pull s y = pull i v -> translate in signed coordinates by i^-1 v, align origin'=i.2-i^-1.act v. f exactly that by composition.
 intro m
 let K:=(m i).1
 let D:=(m i).2
 let T := fun x=> t (affine K 0 x)
 have hm : Lattice.pull K (0:Site P) (Lattice.gauge t (Lattice.pull s v V))=Lattice.gauge T (Lattice.pull i.1 v V):=by
    rw [Work.F05.pull_gauge_zero,pull_pull]
    simp [K,m,reposition,affine,T]
 change ∃ t':Cover→G.El,expandAt D _ = _
 rw [hm,expandAt_gauge]
 refine ⟨fun x=> T ((wrap P) x + D),?_⟩
 congr 1;funext e
 change Step.read _ V (affine i.1 v (wrap P e.1+D))=Step.read _ V (affine i.1 0 (wrap P e.1+i.2))
 apply congrArg (Step.read _ V)
 unfold D m reposition;dsimp only [Equiv.coe_fn_mk];rw [affine,affine,Signed.act_add,Signed.act_add,Signed.act_sub]
 have he : i.1.act ((s⁻¹ * i.1)⁻¹.act (s⁻¹.act v))=v:=by rw [mul_inv_rev,inv_inv,Signed.act_mul,Signed.act_inv,Signed.act_inv]
 rw [he];abel

theorem switch_rep (A B:Camera.Strip (Bedge G P) I)(hA:∀ j, Camera.Pace (A j))(hB:∀ j,Camera.Pace (B j))(he:Camera.roll A 0=0)(hN:Camera.roll B 0=0)(s:Signed)(v:Site P)
   (i:Fin n)(h:Cohort F)(hν:hue (dressed G n) F)(hs:0<σ)(hp:0≤p)(hC: Held (carpet _) σ p F)
   (hu:∀ᶠ x:Cellar I in 𝓝 0, ∃ t:Site P→G.El, offers G (Camera.roll B x)=
     Lattice.gauge t (Lattice.pull s v (offers G (Camera.roll A x)))):
    belt (rescaleFields A) (Camera.tax n (booked F i P))=belt (rescaleFields B) (Camera.tax n (booked F i P)):=by
 rw [wire_taxes _ _ (booked_low P i h hC hp hs),wire_taxes _ _ (booked_low P i h hC hp hs)]
 congr 1
 apply subtended A B hA hB he hN (reposition s v) i h hν hs hp hC
 intro k
 filter_upwards [hu] with x hx
 obtain ⟨t,hT⟩:=hx;rw [hT];exact rewrites s v _ _ _
end YM.RG08.Aggregate
