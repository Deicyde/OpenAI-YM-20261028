import YM.MergeProof.West.Longbow
import YM.Next.RANK.Joule

/-!
# Additional polynomial money -- expose independence before taking any limit over widths
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function MeasureTheory Filter Asymptotics Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset Relation Paint Vac.Numbers Read
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G : Gauge} {H:Purse}
-- recurring eventual costs, Volt bounds existential
variable {f g e z:ℝ→ℝ}
def Bvol (f:ℝ→ℝ):=∃ x, Volt x f
lemma bplus (h:Bvol f)(hp:Bvol g):Bvol fun s=> f s+g s:=by obtain ⟨x,hx⟩:=h; obtain ⟨y,hy⟩:=hp; exact ⟨max x y,(hx.high (le_max_left ..)).plus (hy.high (le_max_right ..))⟩
lemma btimes (h:Bvol f)(hp:Bvol g): Bvol fun s=>f s*g s:= by obtain ⟨_,hv⟩:=h; obtain ⟨_,he⟩:=hp; exact ⟨_,hv.times he⟩
lemma bpulse (a:ℝ):Bvol (bill a):=⟨a,Volt.pulse _⟩
lemma bcert (a:ℝ):Bvol (fun _=> a):=⟨_,Volt.scalar _⟩
lemma bpow (h:Bvol f) (n:ℕ): Bvol (fun s=>f s^n):=by obtain ⟨v,hV⟩:=h; exact ⟨_, hV.power n⟩
lemma bprice (h:Bvol f) (n:ℕ):Bvol (fun s=> Common.priced (f s) n):=by obtain ⟨v,hV⟩:=h; exact ⟨_,hV.lift⟩
lemma bcoin {V:Type*} (S:Clump V) (h:Bvol f): Bvol (fun s=> coinRate S (f s)):=by
   induction S with
   | nil=> exact bcert 0
   | cons i l H=> exact bplus (btimes (bcert ‖(↑i.1:ℂ)‖) (bpow h i.2.length)) H
lemma bcents {V:Type*}(S:Clump V)(h:Bvol f): Bvol (fun s=>West.cents S (f s)):=by
   induction S with
   | nil=>exact bcert 0
   | cons i l H=> exact bplus (btimes (bcert (‖(↑i.1:ℂ)‖*i.2.length)) (bpow h i.2.length)) H
lemma bsigma {V:Type*}(X:V→ℝ→ℝ)(S:Finset V)(h:∀ s,Bvol (X s)):Bvol (fun s=>∑ i∈S, X i s):=by
   induction S using Finset.induction with
   | empty=> simpa using bcert 0
   | insert v s hs IH=> simp_rw [sum_insert hs]; exact bplus (h _) IH
lemma btq (a:ℝ)(h:0<a):Volt a torque:=by
  refine (show Volt a hot from ?_).scale 3; exact ⟨1,zero_le_one,(hotter a h).mono fun s hx=>by rw [one_mul, abs_of_pos (show 0<hot s from Real.exp_pos _)]; exact hx⟩
lemma btvolt (d:ℕ):Volt 1 (fun s=>Common.priced (torque s) d):= (Volt.lift (btq (1/(d+1)) (by positivity))).high (by rw [mul_one_div]; apply (div_le_one (by positivity)).mpr; linarith only)
-- generic growth at foil. independent
lemma candleM {x : ℝ} (f:ℝ→ℝ)(hv:Volt x f)(ε:ℝ): Volt (x+ε) (fun s=> f s*bill ε s):= hv.times (Volt.pulse ε)
lemma gdef (hp:Bvol f) (n:ℕ): Bvol (fun s=> defect (knox s) 1 (f s) n):= by exact btimes hp (btimes (btimes (bcert (n:ℝ)) (bpow (bpulse 1) n)) (bcert 1))
lemma gdef' (s r ε : ℝ) (n:ℕ):defect (knox s) ε r n = defect (knox s) 1 r n * ε:=by unfold defect;ring
lemma gglaring (hp:Bvol f) (n k:ℕ): Bvol (fun s=>West.glare (knox s) 1 (f s) k n):=by
   have h:Bvol knox:=bpulse 1
   exact bplus (bplus (bplus (btimes (btimes (bcert ↑n) (bpow (bplus (btimes hp (bprice h k)) (bcert 1)) n)) (gdef hp k)) (btimes (bcert 1) (btimes (bpow (bpow hp n) 2) (bprice h _)))) (bcert ((n:ℝ)*1))) (btimes (bpow hp n) (btimes (bcert 1) (bprice h _)))
lemma bgant (hp:Bvol f)(n m:ℕ)(L:Clump (Glyph.modes (Fin n))):Bvol (fun s=> grantS L (knox s) 1 (f s) m):=by
   induction L with
   | nil=>exact bcert 0
   | cons i l H=> exact bplus (btimes (bcert ‖(↑i.1:ℂ)‖) (gglaring hp _ _)) H
lemma bgant' (n m:ℕ)(s u ε:ℝ)(L:Clump (Glyph.modes (Fin n))):grantS L (knox s) ε u m=grantS L (knox s) 1 u m*ε:=by
   induction L with
   | nil=>change 0=0*ε; ring
   | cons i l H=>
     let r:= i.2.length; let f:=knox s; let V:=‖(↑i.1:ℂ)‖; change V*West.glare f ε u m r+ _=(V*West.glare f 1 u m r+grantS l _ _ _ _)*ε
     change V*_+grantS l _ _ _ _=_; rw [H]; unfold West.glare defect; ring
lemma ggent (hp:Bvol f)(D n:ℕ): Bvol (fun s=> gentility (knox s) 1 (f s) D n):= bsigma (fun v:modes (Fin n)=> fun s=> grantS (sprout _ (primeLog (Fin n)) v) _ 1 _ D) univ (fun i=> bgant hp n _ _)
lemma ggent' (s u ε:ℝ)(D n:ℕ):gentility (knox s) ε u D n=gentility (knox s) 1 u D n*ε:=by
   unfold gentility; rw [sum_mul]; exact Finset.sum_congr rfl fun i _=> bgant' ..
lemma bgreat (hp:Bvol f)(h:Bvol g)(n:ℕ): Bvol fun s=>grater n (f s) (g s):=btimes (bsigma (fun i:modes (Fin n) => fun s => West.cents (yolk (Fin n) i) (f s)) univ (fun i=> bcents _ hp)) h
lemma grig (u a c:ℝ)(n:ℕ):grater n u (a*c)=grater n u a*c:=by unfold grater;ring

-- cart parameter only.Premature. keep s order notation.
def rents (z:ℝ) (n:ℕ)(s:ℝ) := bill z s ^n * knox s
def qquiet (z:ℝ)(n:ℕ) (s:ℝ) := rents z n s + ∑ i:modes (Fin n), coinRate (yolk (Fin n) i) (rents z n s)
def fq (D n:ℕ):= n*D+∑ i:modes (Fin n), lumpD (yolk (Fin n) i)*(n*D)
def gbt (z:ℝ)(D n:ℕ)(s:ℝ):= gentility (knox s) 1 (qquiet z n s) (fq D n) n
def brr (z:ℝ)(D n:ℕ)(s:ℝ):= grater n (qquiet z n s * Common.priced (torque s) (fq D n) +1) (gbt z D n s)
def brr' (z:ℝ)(D n:ℕ)(s:ℝ):= grater n (rents z n s) (rents z n s*knox s)*Common.priced (knox s) (fq D n)+defect (knox s) 1 (qquiet z n s) (fq D n)
lemma brents (z:ℝ)(n:ℕ):Bvol (rents z n):= btimes (bpow (bpulse z) n) (bpulse 1)
lemma quists (z:ℝ)(n:ℕ):Bvol (qquiet z n):= bplus (brents z n) (bsigma (fun i:modes (Fin n)=>fun s=> coinRate (yolk _ i) (rents z n s)) univ (fun i=> bcoin _ (brents z n)))
lemma glosier (z:ℝ)(D n:ℕ):Bvol (gbt z D n):=ggent (quists z n) _ _
lemma briers (z:ℝ)(D n:ℕ):Bvol (brr z D n):=bgreat (bplus (btimes (quists z n) ⟨_,btvolt _⟩) (bcert 1)) (glosier z D n) n
lemma brierez (z:ℝ)(D n:ℕ): Bvol (brr' z D n):=by
    have h:Bvol knox:= bpulse 1
    exact bplus (btimes (bgreat (brents z n) (btimes (brents z n) h) n) (bprice h _)) (gdef (quists z n) _)
lemma pity (B:Purse)(s:ℝ)(n:ℕ):
    gym B s n=gbt B.credit B.taylor n s*B.sends s ∧ bracelets B s n=brr B.credit B.taylor n s*B.sends s ∧
    blame B s n*Common.priced (knox s) (degrFt B n)+defect (knox s) (B.sends s) (quotaFt B s n) (degrFt B n)= brr' B.credit B.taylor n s*B.sends s:=by
    have hv:gym B s n=gbt B.credit B.taylor n s*B.sends s:= ggent' ..
    refine ⟨hv,?_,?_⟩
    · rw [bracelets,hv,grig];rfl
    rw [blame,grig,gdef']
    change _ * _ * _+ _= (grater n (rentFt B s n) (rentFt B s n *knox s)*Common.priced (knox s) (degrFt B n)+defect (knox s) 1 (quotaFt B s n) (degrFt B n))*B.sends s; ring
end YM.Next.Rank.Tapes.West
