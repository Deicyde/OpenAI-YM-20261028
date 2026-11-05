import YM.RG08.Clef.Delta

/-! # Qualitative surface for recursive Fk Mark algorithm. Slots ident
 still need S factory. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Clef
open Function Finset Jetty Skiff Lattice Isles Forms Pert.Bulk Filter
open Room Gallery Camera MvPolynomial Glyph Weald Quarry Billet Nacre
open scoped Topology BigOperators PowerSeries Classical Matrix
set_option backward.isDefEq.respectTransparency false
variable {I J V:Type}(w:ℕ→ℝ){G:YM.Gauge}{n l:ℕ}

lemma react_injective :Injective (react w):=by
 have hf (q:Dig): undo w (react w q)=q:=by
    change (q ⌾ tilt (ratio w)) ⌾ tilt (fringe w)=q
    rw [show (q ⌾ tilt (ratio w)) ⌾ tilt (fringe w) =q ⌾ (tilt (ratio w) ⌾ tilt (fringe w)) from PowerSeries.subst_comp_subst_apply (tassel _) (tassel _) q,outbound];exact PowerSeries.X_subst q
 exact LeftInverse.injective (f:=react w) hf

lemma repaired [Fintype I][Fintype J][Fintype V] {L:Quarry.Loom I J V}(x:Tray (Market J)):
 portrait L (shuttle w x)=shuttle w (portrait L x):=by
 have he:(portrait L (shuttle w x)).base=(portrait L x).base:=rfl
 have ht:(portrait L (shuttle w x)).get=(shuttle w (portrait L x)).get:=by
    funext i;apply react_injective w
    rw [show (shuttle w (portrait L x)).get _=via _ _ _ from rfl,returning]
    exact scales w _ _
 generalize hY:portrait L (shuttle w x)=y, hZ:shuttle w (portrait L x)=z at *
 have hp : y.base=z.base:=by rw [←hZ];exact he
 obtain ⟨xs,b,hb⟩:=y; obtain ⟨ys,c,hc⟩:=z; change xs=ys at hp;change b=c at ht;congr
lemma repaired_art (x:Tray (Market I))(u:Tray (Market J)):Quarry.art (shuttle w x) (shuttle w u)=shuttle w (Quarry.art x u):=by
 unfold Quarry.art shuttle via;congr 1;funext i;rcases i with ⟨z,i|i⟩<;>rfl

-- calls is at own g. No restriction d.
lemma royalty {P:GrainS (Ed G Cover)}(hP:Calls l P)(ht:Skiff.Lit l P):Calls l (film w P):=by
 intro f x u r
 rw [←rap w ht,←rap w ht, ←repaired,←repaired_art w,hP ..]

-- qualitative operations for building projection-null residual detectors.
lemma Permit_hush (d l:ℕ)[Fintype I]:Weald.Permit d l (0:GrainS (Market I)):=⟨fun _ _ h=>False.elim (h rfl),fun _ _ _=>Forms.Sym.zero,fun _ _=>⟨hush,1,one_pos,0,le_rfl,tin⟩⟩
lemma Calls_hush: Calls l (0:GrainS (Ed G Cover)):=by intro f x b r;ext e:1; unfold Weald.mint;rw [PowerSeries.coeff_mk,PowerSeries.coeff_mk];simp only [crown,Pi.zero_apply,summit_blank]

lemma Permit_add {d:ℕ}[Fintype I]{P Q:GrainS (Market I)}(h:Weald.Permit d l P)(he:Weald.Permit d l Q):Weald.Permit d l (P+Q):=by
 constructor
 · intro i n;contrapose!;intro he1;have ht:P i n=0:=by contrapose! he1;exact h.lit _ _ he1
   change P i n+Q i n=0;rw [ht,zero_add]; contrapose! he1;exact he.lit _ _ he1
 · intro f i n;exact (h.fine f _ _).add (he.fine f _ _)
 intro e n;obtain ⟨hv,k,hk,p,hp,H⟩:=h.price e n;obtain ⟨hh,t,hT,q,hq,V⟩:=he.price e n
 let z:=min k t;have hZ:0<z:=lt_min hk hT
 exact ⟨hv.add hh,z,hZ,p+q,add_nonneg hp hq,(H.mono (ht:=hZ) (min_le_left ..) le_rfl (fun _=>le_rfl) le_rfl).add (V.mono (min_le_right ..) le_rfl (fun _=>le_rfl) le_rfl) hp hq⟩
lemma Permit_smul {d:ℕ}[Fintype I]{P:GrainS (Market I)}(he:Weald.Permit d l P)(a:ℝ):Weald.Permit d l (a • P):=by
 constructor
 · intro i n;contrapose!;intro h; change a • P i n=0;rw [show P i n=0 from ?_,smul_zero];contrapose! h;exact he.lit i n h
 · intro f i n; exact (he.fine f i n).smul _
 intro i n;obtain ⟨h,k,hK,p,hp,hT⟩:=he.price i n
 exact ⟨h.smul a,k,hK,|a| *p,mul_nonneg (abs_nonneg _) hp,hT.smul _⟩
lemma Permit_lend {d:ℕ}[Fintype I]{P:GrainS (Market I)}(he:Weald.Permit d l P):Weald.Permit d l (film w P):=by
 constructor
 · exact lit_film w he.lit
 · intro f i n; change Forms.Sym (during f (∑ j∈range (i+1),Nacre.dues w j n i • P j n));rw [Trickle.during_sum]
   have hs{ι : Type}(s:Finset ι)(A:ι→Flake n (Market I))(h:∀ i, Forms.Sym (A i)):Forms.Sym (s.sum A):=by
      induction s using Finset.induction_on with
      | empty=>exact Forms.Sym.zero
      | @insert i s hi ih=> rw [Finset.sum_insert hi];exact (h i).add ih
   apply hs; intro k; exact (he.fine f k n).smul _
 intro e n; obtain ⟨σ,h,C,hc,hp⟩:=he.price.license he.lit e
 unfold film; refine ⟨Lyrics.sum (range _) (fun i hi=> ((he.price i n).1).smul _),σ,h,(∑ i∈range (e+1),|Nacre.dues w i n e| *C),sum_nonneg (fun i _=>mul_nonneg (abs_nonneg _) hc),Sings.sum (range _) (fun i hi=>(hp i (by simpa using hi) n).smul _) (fun i _=>mul_nonneg (abs_nonneg _) hc)⟩
lemma mint_lin {P Q:GrainS I}(A:Tray I)(f:Pearl)(l:ℕ)(a:ℝ):Weald.mint l (P+a • Q) f A=Weald.mint l P f A+a • Weald.mint l Q f A:=by
 ext e :1; unfold Weald.mint;rw [map_add,PowerSeries.coeff_smul,PowerSeries.coeff_mk,PowerSeries.coeff_mk,PowerSeries.coeff_mk]
 simp only [crown,Pi.add_apply,Pi.smul_apply]
 have he {n:ℕ}{P Q:Pack n I}:summit (P+a • Q) f A=summit P f A+a • summit Q f A:=by
    unfold summit Gallery.volume during;simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_smul,← smul_smul,Finset.smul_sum,sum_add_distrib] -- smul_eq_mul on a only? smul_eq_mul ℝ ring? Dig group? Module ℝ ≠ mul, defeq?
 simp_rw [he,Finset.sum_add_distrib,← Finset.smul_sum,tap,map_add,PowerSeries.coeff_smul,Finset.sum_add_distrib,←Finset.smul_sum]
lemma Calls_lin {P Q:GrainS (Ed G Cover)}(hP:Calls l P)(hQ:Calls l Q)(a:ℝ):Calls l (P+a • Q):=by intro f x y d;rw [mint_lin,mint_lin,hP f x y d,hQ f x y d]
lemma Calls_smul {P:GrainS (Ed G Cover)}(hP:Calls l P)(a:ℝ):Calls l (a • P):=by rw [←zero_add (a • P)];exact Calls_lin Calls_hush hP a
end YM.RG08.Clef
