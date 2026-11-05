import YM.RG08.Fete.Oboes
import YM.Planned.PRIMARY_INTEGRAL_295.Pearl
/-!
# Recover the field from its section stencil by exact composition in the projected rank.
 No h-dependent chart radius assumption. Before regulator. 
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Fete
open Function Finset Jetty Lattice Isles Forms Pert.Bulk Skiff Trickle
open Room Gallery Camera Glyph Quarry Weald Hatch Carrel Laurent Filter Stationary Flint
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Lagoon Trill Exterior RG Precision
open scoped Classical ContDiff Topology BigOperators ENNReal Matrix.Norms.Frobenius ComplexConjugate
variable {G:Gauge}{d n p l e D k q i:ℕ}{σ B:ℝ}{S:Finset Cover}
local notation "E"=>Ed G Cover
local notation "Y"=>Snap G d
variable {X:Labels.Frame G d}
def opus (T:SectionData X)(c:Accent X)(n:ℕ):Pack n E:=bandF window (ton (astro T c.ear) n) (concert c.test.play)
-- project only if l_out≥l_c & shift matches e. grouping grants has true factor. assemble all n & test. h.V
lemma opus_power (T:SectionData X)(c:Accent X){n:ℕ}(v:Pearl)(x:Fin n→Fin (p+1))(z:Y): sonic (opus T c n) v (fun j=>pluck (x j).val z)=loot (concert c.test.play) 0 v * Tensor.coeff (astro T c.ear) n 0 (fun j=>Tensor.diagonal (Tensor.coeff flume (x j).val 0) z):=by
 unfold sonic tote;rw [opus,band_pay,ton_comp];simp_rw [flakes,flume_tint];rfl
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 300000
lemma opus_synth (T:SectionData X)(c:Accent X)(f:Pearl)(X0:Y):
 (∑ n∈range (p+1),Tensor.diagonal (harrow (opus T c n) f p d) X0) =loot (concert c.test.play) 0 f * Tensor.diagonal (Tensor.coeff (astro T c.ear ∘ flume) p 0) X0:=by
 have hz(n):Lyrics (opus T c n) ∧ ∃ C:ℝ,0≤C∧Sings (stance _) d (zero_lt_one:0<(1:ℝ)) (opus T c n) C:=band_price _ _ _ _ c.test.held
 choose L a Q A using hz
 rw [atop (flume_smooth.of_le le_top) ((lamp T c.ear).of_le le_top) flume0,mul_sum];apply sum_congr rfl;intro i _
 rw [harrow_diag (L i) (A i) (Q i),grants,mul_sum];apply sum_congr rfl;intro j _; rw [opus_power]
lemma opus_harm (T:SectionData X)(c:Accent X)(f:Pearl):
 (∑ n∈range (p+1),harrow (opus T c n) f p d) =loot (concert c.test.play) 0 f • Tensor.coeff (astro T c.ear ∘ flume (d:=d)) p 0:=by
 let Z:=@flume G d T.stencil
 have ht:Pace (astro T c.ear ∘ Z):=(show ContDiffAt ℝ ω (astro T c.ear) (flume (0:Y)) by rw [flume0];exact lamp T c.ear).comp (0:Y) flume_smooth -- Z0
 have hb(n):Tensor.Sym (harrow (opus T c n) f p d):=by obtain ⟨H,C,hC,G⟩:= band_price window (ton (astro T c.ear) n) (concert c.test.play) zero_lt_one c.test.held;exact harrow_sym H G hC _
 apply Tensor.ext_diag _ _ (fun v t=>?_) (fun v t=> congrArg (loot (concert c.test.play) 0 f • ·) (Tensor.coeff_symm (ht.of_le (show (p:WithTop ℕ∞)≤ω from le_top)) v t))
 · funext X; unfold Tensor.diagonal;rw [_root_.sum_apply,_root_.smul_apply,smul_eq_mul];exact opus_synth T c f X
 rw [_root_.sum_apply,_root_.sum_apply];apply sum_congr rfl;intro i _;exact hb i v t

set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 700000
lemma opus_tile (T:SectionData X)(a:X.Index)(H:Hol G)(h:T.Sound H)(hk:k≤d)(hl:p≤d):
 (gradePart (k,p) (X.basis a)).val= tile (paintBand (Tensor.coeff (astro T a ∘ (@flume G d T.stencil)) p 0)) k:=by
 let f:= column T a ∘ @localLane G d T.stencil
 have he : f=Complex.ofRealCLM ∘ astro T a ∘ @flume G d T.stencil :=by funext v;change column T a _=(astro T a (flume v):ℂ);rw [astro_live H T h,flume_full]
 rw [show X.basis a= archive (Film.still T h (Place.copy X a)) from ?_,Parts.capture _ hk hl];swap
 · rw [Film.corner T h (Place.copy X a)];apply X.coords.injective;rw [X.coords_basis,X.coords.apply_symm_apply]; rfl
 change tile (Tensor.coeff f _ 0) k=_
 rw [he]; let g:=astro T a ∘ @flume G d T.stencil
 change tile (Tensor.coeff (Complex.ofRealCLM ∘ g) _ 0) k=_
 have h1:Pace g:=(show ContDiffAt ℝ ω (astro T a) (flume (0:Y)) by rw [flume0];exact lamp ..).comp (0:Y) flume_smooth
 have hA:= Complex.ofRealCLM.iteratedFDeriv_comp_left h1 (i:=p) (mod_cast le_top)
 unfold paintBand Tensor.coeff;rw [hA];apply congrArg (tile · k);ext1 v
 rw [_root_.smul_apply]; change _=Complex.ofRealCLM ((p.factorial:ℝ)⁻¹ • _);rw [_root_.map_smul];rfl
lemma opus_price (T:SectionData X){H:Hol G}(h:T.Sound H)(c y:Accent X)(v:y.test.play=c.test.play):
 (∑ n ∈ range ((X.grades y.ear).2+1),pix X y.ear y.test.play (opus T c n))= if c.ear=y.ear then 1 else 0:=by
 let p:=(X.grades y.ear).2;let k:=(X.grades y.ear).1
 unfold pix;rw [←map_sum,opus_harm,cello_dual,concert_at,if_pos v.symm,one_smul]
 let M:=Tensor.coeff (astro T c.ear ∘ @flume G d _) p 0
 have hh:=tally_label X M (opus_tile (k:=k) T c.ear H h (X.bound _) ((grades_two X y.ear).trans (X.bound y.ear))) y.ear
 apply Complex.ofReal_injective
 change (tally X p k _ M:ℂ)=_;rw [hh]
 by_cases hx:c.ear=y.ear
 · rw [if_pos hx,hx,show (k,p)=(X.grades y.ear) from rfl,gradePart_self _ _ (X.pure _),X.coords_basis,Pi.single_eq_same,Complex.ofReal_one]
 rw [if_neg hx,Complex.ofReal_zero]
 by_cases he:X.grades c.ear=(k,p)
 · rw [←he,gradePart_self _ _ (X.pure _),X.coords_basis,Pi.single_eq_of_ne (Ne.symm hx)]
 rw [gradePart_zero _ _ _ (Ne.symm he) (X.pure _),map_zero];rfl -- he.symm on ≠
lemma opus_curve (T:SectionData X)(c y:Accent X)(hv:y.test.play≠c.test.play):
 (∑ n∈ range ((X.grades y.ear).2+1),pix X y.ear y.test.play (opus T c n))=0:=by unfold pix;rw [←map_sum,opus_harm,cello_dual,concert_at,if_neg (Ne.symm hv),zero_smul,map_zero]
lemma opus_low (T:SectionData X)(a:Accent X)(h:Bid.pop T)(hn:n<(X.grades a.ear).2):opus T a n=0:=by
 unfold opus bandF ton;rw [silence T a.ear h n hn];simp
lemma opus_mask (i:X.Index)(v:pedal): pix X i v (0:Trill.Gras G n)=0:=by
 unfold pix harrow;rw [show grants (0:_) _ _ d=(fun _=>0) from ?_,Tensor.coeff_zero,map_zero]; funext x;unfold grants;apply sum_eq_zero;intro _ _; unfold sonic tote; simp
/-- All-order S section. Through any own-g coefficient, requested Accent X and basis. -/
theorem encore_project (T:SectionData X){H:Hol G}(h:T.Sound H)(ht:Bid.pop T)(e:ℕ)(c y:Accent X): Trill.project X (encore T c) e y=if e=0 ∧ c=y then 1 else 0:=by
 let p:=(X.grades c.ear).2;let q:=(X.grades y.ear).2
 unfold project encore;change (∑ n∈range (q+1),if q-n≤e then pix X y.ear y.test.play (if n=e-(q-n)+p then opus T c n else 0) else 0)=_
 by_cases hp:q=e+p
 · rw [show q=e+p from hp] -- maybe weights formulas; fold
   have hh: (∑ n∈range (e+p+1),if e+p-n≤e then pix X y.ear y.test.play (if n=e-(e+p-n)+p then opus T c n else 0) else 0) = ∑ n∈range (q+1),pix X y.ear y.test.play (opus T c n):=by
    rw [hp];apply sum_congr rfl;intro i hi;have hy := mem_range.mp hi
    by_cases hk:p ≤ i
    · rw [if_pos (by omega),if_pos (by omega)]
    rw [if_neg (by omega),opus_low T c ht (by change i<p;omega),opus_mask]
   rw [hh];by_cases hv:y.test.play=c.test.play
   · rw [opus_price T h c y hv];split_ifs with h' h'' h'' <;> try rfl
     · exfalso; apply h''
       have hh:p=q:=congrArg (fun i=>(X.grades i).2) h'
       exact ⟨by omega,by rcases c with ⟨ea,⟨vv,_⟩,_⟩;rcases y with ⟨eb,⟨vw,_⟩,_⟩; dsimp only at h' hv;cases hv;subst eb; rfl⟩
     exact False.elim (h' (h''.2 ▸ rfl))
   rw [opus_curve T c y hv,if_neg (show ¬(e=0 ∧ c=y) from fun h=>hv (h.2 ▸ rfl))]
 -- no n term
 rw [sum_eq_zero (fun i hi=>?_ ),if_neg (fun h=>?_)]
 · exfalso;apply hp;rw [h.1,zero_add];unfold p q;rw [h.2]
 have hi:= mem_range.mp hi;split_ifs with H hh;omega; exact opus_mask ..;rfl
end YM.RG08.Fete
