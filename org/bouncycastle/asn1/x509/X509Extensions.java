package org.bouncycastle.asn1.x509;

import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Vector;

import org.bouncycastle.asn1.ASN1Boolean;
import org.bouncycastle.asn1.ASN1EncodableVector;
import org.bouncycastle.asn1.ASN1Object;
import org.bouncycastle.asn1.ASN1ObjectIdentifier;
import org.bouncycastle.asn1.ASN1OctetString;
import org.bouncycastle.asn1.ASN1Primitive;
import org.bouncycastle.asn1.ASN1Sequence;
import org.bouncycastle.asn1.ASN1TaggedObject;
import org.bouncycastle.asn1.DERSequence;

/**
 * deprecated use {@link Extensions}
 */
public class X509Extensions
    extends ASN1Object
{
    /**
     * NoRevAvail extension in attribute certificates.
     *  deprecated use X509Extension value.
     */
    public static final ASN1ObjectIdentifier NoRevAvail = new ASN1ObjectIdentifier("2.5.29.56");
    
    private Hashtable               extensions = new Hashtable();
    private Vector                  ordering = new Vector();

    public static X509Extensions getInstance(
        ASN1TaggedObject obj,
        boolean          explicit)
    {
        return getInstance(ASN1Sequence.getInstance(obj, explicit));
    }

    public static X509Extensions getInstance(
        Object  obj)
    {
        if (obj == null || obj instanceof X509Extensions)
        {
            return (X509Extensions)obj;
        }

        if (obj instanceof ASN1Sequence)
        {
            return new X509Extensions((ASN1Sequence)obj);
        }

        if (obj instanceof Extensions)
        {
            return new X509Extensions((ASN1Sequence)((Extensions)obj).toASN1Primitive());
        }

        if (obj instanceof ASN1TaggedObject)
        {
            return getInstance(((ASN1TaggedObject)obj).getObject());
        }

        throw new IllegalArgumentException("illegal object in getInstance: " + obj.getClass().getName());
    }

    /**
     * Constructor from ASN1Sequence.
     *
     * the extensions are a list of constructed sequences, either with (OID, OctetString) or (OID, Boolean, OctetString)
     */
    public X509Extensions(
        ASN1Sequence  seq)
    {
        Enumeration e = seq.getObjects();

        while (e.hasMoreElements())
        {
            ASN1Sequence            s = ASN1Sequence.getInstance(e.nextElement());

            if (s.size() == 3)
            {
                extensions.put(s.getObjectAt(0), new X509Extension(ASN1Boolean.getInstance(s.getObjectAt(1)), ASN1OctetString.getInstance(s.getObjectAt(2))));
            }
            else if (s.size() == 2)
            {
                extensions.put(s.getObjectAt(0), new X509Extension(false, ASN1OctetString.getInstance(s.getObjectAt(1))));
            }
            else
            {
                throw new IllegalArgumentException("Bad sequence size: " + s.size());
            }

            ordering.addElement(s.getObjectAt(0));
        }
    }

    /**
     * constructor from a table of extensions.
     * <p>
     * it's is assumed the table contains OID/String pairs.
     */
    public X509Extensions(
        Hashtable  extensions)
    {
        this(null, extensions);
    }

    /**
     * Constructor from a table of extensions with ordering.
     * <p>
     * It's is assumed the table contains OID/String pairs.
     * deprecated use Extensions
     */
    public X509Extensions(
        Vector      ordering,
        Hashtable   extensions)
    {
        Enumeration e;

        if (ordering == null)
        {
            e = extensions.keys();
        }
        else
        {
            e = ordering.elements();
        }

        while (e.hasMoreElements())
        {
            this.ordering.addElement(ASN1ObjectIdentifier.getInstance(e.nextElement()));
        }

        e = this.ordering.elements();

        while (e.hasMoreElements())
        {
            ASN1ObjectIdentifier     oid = ASN1ObjectIdentifier.getInstance(e.nextElement());
            X509Extension           ext = (X509Extension)extensions.get(oid);

            this.extensions.put(oid, ext);
        }
    }
    
    /**
     * return an Enumeration of the extension field's object ids.
     */
    public Enumeration oids()
    {
        return ordering.elements();
    }

    /**
     * return the extension represented by the object identifier
     * passed in.
     *
     * @return the extension if it's present, null otherwise.
     */
    public X509Extension getExtension(
        ASN1ObjectIdentifier oid)
    {
        return (X509Extension)extensions.get(oid);
    }

    /**
     * <pre>
     *     Extensions        ::=   SEQUENCE SIZE (1..MAX) OF Extension
     *
     *     Extension         ::=   SEQUENCE {
     *        extnId            EXTENSION.&amp;id ({ExtensionSet}),
     *        critical          BOOLEAN DEFAULT FALSE,
     *        extnValue         OCTET STRING }
     * </pre>
     */
    public ASN1Primitive toASN1Primitive()
    {
        ASN1EncodableVector     vec = new ASN1EncodableVector();
        Enumeration             e = ordering.elements();

        while (e.hasMoreElements())
        {
            ASN1ObjectIdentifier    oid = (ASN1ObjectIdentifier)e.nextElement();
            X509Extension           ext = (X509Extension)extensions.get(oid);
            ASN1EncodableVector     v = new ASN1EncodableVector();

            v.add(oid);

            if (ext.isCritical())
            {
                v.add(ASN1Boolean.TRUE);
            }

            v.add(ext.getValue());

            vec.add(new DERSequence(v));
        }

        return new DERSequence(vec);
    }

    public boolean equivalent(
        X509Extensions other)
    {
        if (extensions.size() != other.extensions.size())
        {
            return false;
        }

        Enumeration     e1 = extensions.keys();

        while (e1.hasMoreElements())
        {
            Object  key = e1.nextElement();

            if (!extensions.get(key).equals(other.extensions.get(key)))
            {
                return false;
            }
        }

        return true;
    }

    public ASN1ObjectIdentifier[] getExtensionOIDs()
    {
        return toOidArray(ordering);
    }
    
    public ASN1ObjectIdentifier[] getNonCriticalExtensionOIDs()
    {
        return getExtensionOIDs(false);
    }

    public ASN1ObjectIdentifier[] getCriticalExtensionOIDs()
    {
        return getExtensionOIDs(true);
    }

    private ASN1ObjectIdentifier[] getExtensionOIDs(boolean isCritical)
    {
        Vector oidVec = new Vector();

        for (int i = 0; i != ordering.size(); i++)
        {
            Object oid = ordering.elementAt(i);

            if (((X509Extension)extensions.get(oid)).isCritical() == isCritical)
            {
                oidVec.addElement(oid);
            }
        }

        return toOidArray(oidVec);
    }

    private ASN1ObjectIdentifier[] toOidArray(Vector oidVec)
    {
        ASN1ObjectIdentifier[] oids = new ASN1ObjectIdentifier[oidVec.size()];

        for (int i = 0; i != oids.length; i++)
        {
            oids[i] = (ASN1ObjectIdentifier)oidVec.elementAt(i);
        }
        return oids;
    }
}
